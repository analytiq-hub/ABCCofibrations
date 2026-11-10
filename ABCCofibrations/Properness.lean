/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Extension

/-!
# Properness (§1.8)

A precofibration category is *left proper* (axiom PCF, Definition 1.8.1(1))
if pushouts along cofibrations with cofibrant domain exist for arbitrary
maps, and preserve weak equivalences. A map `f : A ⟶ B` is *left proper*
(Definition 1.8.3(1)) if pushouts along `f` exist and pushing a weak
equivalence `r : C₁ ⟶ C₂` under `A` along `f` gives a weak equivalence:
in the diagram of pushout squares

```
A --g--> C₁ --r--> C₂
|f       |j₁       |j₂
B --h--> D₁ --r'-> D₂
```

`r'` is a weak equivalence whenever `r` is.

We prove that a precofibration category in which all objects are cofibrant is
left proper (by excision, Lemma 1.4.2(1)), and Theorem 1.8.4(1)(a): in a left
proper precofibration category, every cofibration with cofibrant domain is a
left proper map.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

section LeftProperMap

variable {C : Type u} [Category.{v} C] [CategoryWithWeakEquivalences C]

/-- A map is *left proper* (Definition 1.8.3(1)) if its pushouts along all maps
exist, and weak equivalences under its domain are preserved by pushout along it.
The condition is stated for every pushout square, not a chosen one. -/
structure IsLeftProper {A B : C} (f : A ⟶ B) : Prop where
  hasPushout ⦃D : C⦄ (g : A ⟶ D) : HasPushout g f
  weakEquivalence ⦃C₁ C₂ D₁ D₂ : C⦄ {g : A ⟶ C₁} {r : C₁ ⟶ C₂} {j₁ : C₁ ⟶ D₁}
    {h : B ⟶ D₁} {j₂ : C₂ ⟶ D₂} {r' : D₁ ⟶ D₂}
    (sq₁ : IsPushout g f j₁ h) (sq₂ : IsPushout r j₁ j₂ r') [WeakEquivalence r] :
    WeakEquivalence r'

namespace IsLeftProper

/-- Left proper maps are stable under pushout: if `f` is left proper and `j` is
the pushout of `f` along `u`, then `j` is left proper. Both conditions follow
by pasting with the square defining `j`. -/
theorem of_isPushout {A A' B B' : C} {f : A ⟶ B} (hf : IsLeftProper f) {u : A ⟶ A'}
    {j : A' ⟶ B'} {h : B ⟶ B'} (sq : IsPushout u f j h) : IsLeftProper j where
  hasPushout D g := by
    have := hf.hasPushout (u ≫ g)
    exact (IsPushout.of_left' (IsPushout.of_hasPushout (u ≫ g) f) sq).hasPushout
  weakEquivalence _ _ _ _ _ _ _ _ _ _ sq₁ sq₂ _ :=
    hf.weakEquivalence (sq.paste_horiz sq₁) sq₂

/-- Left proper maps are stable under composition, by vertical pushout pasting:
push `r` first along the pushout of `f`, then along the pushout of `f₂`. -/
theorem comp {A B B' : C} {f : A ⟶ B} {f₂ : B ⟶ B'} (hf : IsLeftProper f)
    (hf₂ : IsLeftProper f₂) : IsLeftProper (f ≫ f₂) where
  hasPushout D g := by
    have := hf.hasPushout g
    have := hf₂.hasPushout (pushout.inr g f)
    exact ((IsPushout.of_hasPushout g f).paste_vert
      (IsPushout.of_hasPushout (pushout.inr g f) f₂)).hasPushout
  weakEquivalence {C₁ C₂ D₁ D₂ g r j₁ h j₂ r'} sq₁ sq₂ _ := by
    have := hf.hasPushout g
    let t := IsPushout.of_hasPushout g f
    -- The square from the pushout of `f` to `D₁` is a pushout of `f₂`.
    have kb := IsPushout.of_top' sq₁ t
    set k := t.desc j₁ (f₂ ≫ h) _
    have hk : pushout.inl g f ≫ k = j₁ := t.inl_desc _ _ _
    -- Push `r` along the pushout of `f`.
    have := hf.hasPushout (g ≫ r)
    have sqR := IsPushout.of_left' (IsPushout.of_hasPushout (g ≫ r) f) t
    have := hf.weakEquivalence t sqR
    -- Then along `k`, which is a pushout of `f₂`, hence left proper.
    have sq₂' : IsPushout r (pushout.inl g f ≫ k) j₂ r' := by rw [hk]; exact sq₂
    exact (hf₂.of_isPushout kb).weakEquivalence IsPushout.of_id_fst
      (IsPushout.of_top' sq₂' sqR)

end IsLeftProper

end LeftProperMap

namespace ABCPrecofibrationCategory

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- Axiom PCF (Definition 1.8.1(1)): pushouts of cofibrations with cofibrant
domain exist along arbitrary maps, and the pushout of a weak equivalence along
such a cofibration is a weak equivalence. Compared with CF3, the other corner
`D` need not be cofibrant. -/
class LeftProper : Prop where
  hasPushout {A B D : C} (i : A ⟶ B) (r : A ⟶ D) [IsCofibrant A] [Cofibration i] :
    HasPushout i r
  weakEquivalence_of_isPushout {A B D E : C} {i : A ⟶ B} {r : A ⟶ D} {r' : B ⟶ E}
    {j : D ⟶ E} (h : IsPushout i r r' j) [IsCofibrant A] [Cofibration i] [WeakEquivalence r] :
    WeakEquivalence r'

variable {C}

/-- A precofibration category in which every object is cofibrant is left
proper, by CF3 and excision. -/
theorem leftProper_of_forall_isCofibrant [∀ X : C, IsCofibrant X] : LeftProper C where
  hasPushout i r := hasPushout i r
  weakEquivalence_of_isPushout h := weakEquivalence_of_isPushout_of_cofibration h

/-- **Theorem 1.8.4(1)(a).** In a left proper precofibration category, a
cofibration with cofibrant domain is a left proper map.

Factor `g : A ⟶ C₁` as a cofibration `f₁ : A ⟶ Z` followed by a weak
equivalence `s`, push `i` out along `f₁` to a cofibration `i'` with cofibrant
domain `Z`, and apply PCF along `i'` to `s` and to `s ≫ r`; two out of three
gives `r'`. -/
theorem isLeftProper_of_cofibration [LeftProper C] {A B : C} [IsCofibrant A]
    (i : A ⟶ B) [Cofibration i] : IsLeftProper i where
  hasPushout D g := by
    have := LeftProper.hasPushout i g
    exact hasPushout_symmetry i g
  weakEquivalence {C₁ C₂ D₁ D₂ g r j₁ h j₂ r'} sq₁ sq₂ _ := by
    obtain ⟨Z, f₁, s, hf₁, hs, hfac⟩ := factorization g
    have := cofibrant_target f₁
    have := cofibrant_target i
    -- Push `i` out along the cofibration `f₁`.
    let sq₀ := IsPushout.of_hasPushout f₁ i
    have : Cofibration (pushout.inl f₁ i) := cofibration_of_isPushout sq₀.flip
    -- The square from `Z` to `C₁` is a pushout, by pasting with `sq₀`.
    have outer : IsPushout (f₁ ≫ s) i j₁ h := by rw [hfac]; exact sq₁
    have sqL := IsPushout.of_left' outer sq₀
    -- PCF along `pushout.inl f₁ i`, applied to `s` and to `s ≫ r`.
    have := LeftProper.weakEquivalence_of_isPushout sqL.flip
    have hsr' := LeftProper.weakEquivalence_of_isPushout (sqL.paste_horiz sq₂).flip
    exact (weakEquivalence_precomp_iff _ r').1 hsr'

/-- Isomorphisms are left proper maps. -/
theorem isLeftProper_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : IsLeftProper f where
  hasPushout D g :=
    (IsPushout.of_vert_isIso (f := g) (g := f) (inl := 𝟙 D) (inr := inv f ≫ g)
      ⟨by simp⟩).hasPushout
  weakEquivalence {C₁ C₂ D₁ D₂ g r j₁ h j₂ r'} sq₁ sq₂ _ := by
    have := sq₁.isIso_inl_of_isIso
    have := sq₂.isIso_inl_of_isIso
    have := weakEquivalence_of_isIso j₁
    have := weakEquivalence_of_isIso j₂
    have : WeakEquivalence (j₁ ≫ r') := by
      rw [← sq₂.w]
      infer_instance
    exact weakEquivalence_of_precomp j₁ r'

/-- **Theorem 1.8.4(1)(b).** In a left proper precofibration category, every map
factors as a left proper map followed by a weak equivalence.

Take a cofibrant replacement `a : A' ⟶ A`, factor `a ≫ f` as a cofibration
`f₁` followed by a weak equivalence `r₁`, and push `f₁` out along `a`. The
pushout of `f₁` is left proper by part (a) and stability under pushout, the
pushout of `a` is a weak equivalence by PCF, and two out of three handles the
induced map. -/
theorem exists_leftProper_factorization [LeftProper C] {A B : C} (f : A ⟶ B) :
    ∃ (Y : C) (f' : A ⟶ Y) (r : Y ⟶ B), IsLeftProper f' ∧ WeakEquivalence r ∧ f' ≫ r = f := by
  obtain ⟨A', a, hA', ha⟩ := exists_cofibrant_replacement A
  obtain ⟨Z, f₁, r₁, hf₁, hr₁, hfac⟩ := factorization (a ≫ f)
  have := LeftProper.hasPushout f₁ a
  let sq := IsPushout.of_hasPushout f₁ a
  have hinl : WeakEquivalence (pushout.inl f₁ a) := LeftProper.weakEquivalence_of_isPushout sq
  let r : pushout f₁ a ⟶ B := pushout.desc r₁ f hfac
  have hr : WeakEquivalence r :=
    weakEquivalence_of_precomp_of_fac (pushout.inl_desc r₁ f hfac)
  exact ⟨pushout f₁ a, pushout.inr f₁ a, r,
    (isLeftProper_of_cofibration f₁).of_isPushout sq.flip, hr, pushout.inr_desc r₁ f hfac⟩

/-- **Theorem 1.8.4(1)(c).** In a left proper precofibration category, trivial
left proper maps are stable under pushout: the pushout `j` of a left proper
weak equivalence `i` along any map is again a left proper weak equivalence.

Factor the map as a left proper `f'` followed by a weak equivalence `r`. The
pushout of `i` along `f'` is a weak equivalence because `f'` is left proper,
pushing `r` along it gives a weak equivalence because `i` is left proper, and
two out of three gives `j`. -/
theorem _root_.ABCCofibrations.IsLeftProper.weakEquivalence_of_isPushout [LeftProper C]
    {A B D E : C} {i : A ⟶ B} (hi : IsLeftProper i) [WeakEquivalence i]
    {f : A ⟶ D} {j : D ⟶ E} {g : B ⟶ E}
    (h : IsPushout f i j g) : IsLeftProper j ∧ WeakEquivalence j := by
  refine ⟨hi.of_isPushout h, ?_⟩
  obtain ⟨Y, f', r, hf', hr, hfac⟩ := exists_leftProper_factorization f
  have := hi.hasPushout f'
  let sqP := IsPushout.of_hasPushout f' i
  -- The pushout of `i` along the left proper map `f'` is a weak equivalence.
  have : WeakEquivalence (pushout.inl f' i) :=
    hf'.weakEquivalence IsPushout.of_id_fst sqP.flip
  -- Pushing `r` along it is a weak equivalence, since `i` is left proper.
  have outer : IsPushout (f' ≫ r) i j g := by rw [hfac]; exact h
  have sqL := IsPushout.of_left' outer sqP
  have := hi.weakEquivalence sqP sqL
  have : WeakEquivalence (r ≫ j) := by
    rw [sqL.w]
    infer_instance
  exact weakEquivalence_of_precomp r j

/-- **Proposition 1.8.5(1).** In a left proper precofibration category, a weak
equivalence is left proper exactly when its pushouts along all maps exist and
are weak equivalences. The forward direction is Theorem 1.8.4(1)(c); the
converse uses pasting and two out of three, and needs no properness. -/
theorem isLeftProper_iff_of_weakEquivalence [LeftProper C] {A B : C} (i : A ⟶ B)
    [WeakEquivalence i] :
    IsLeftProper i ↔ (∀ ⦃D : C⦄ (g : A ⟶ D), HasPushout g i) ∧
      ∀ ⦃D E : C⦄ {g : A ⟶ D} {j : D ⟶ E} {k : B ⟶ E}, IsPushout g i j k →
        WeakEquivalence j := by
  constructor
  · intro hi
    exact ⟨hi.hasPushout, fun _ _ _ _ _ h ↦ (hi.weakEquivalence_of_isPushout h).2⟩
  · rintro ⟨hex, hwe⟩
    refine ⟨hex, fun C₁ C₂ D₁ D₂ g r j₁ h j₂ r' sq₁ sq₂ _ ↦ ?_⟩
    have := hwe sq₁
    have := hwe (sq₁.paste_horiz sq₂)
    have : WeakEquivalence (j₁ ≫ r') := by
      rw [← sq₂.w]
      infer_instance
    exact weakEquivalence_of_precomp j₁ r'

section LeftProperCofibrations

variable (C) in
/-- A type synonym for `C`, carrying the left proper maps as cofibrations
(and the same weak equivalences and initial object). -/
def LeftProperCofibrations : Type u := C

instance : Category.{v} (LeftProperCofibrations C) := inferInstanceAs (Category.{v} C)

instance : CategoryWithCofibrations (LeftProperCofibrations C) where
  cofibrations _ _ f := IsLeftProper (C := C) f

instance : CategoryWithWeakEquivalences (LeftProperCofibrations C) where
  weakEquivalences := weakEquivalences C

instance : HasInitial (LeftProperCofibrations C) := inferInstanceAs (HasInitial C)

/-- **Theorem 1.8.4(1)(d).** If `C` is a left proper precofibration category,
then `C` with the same weak equivalences and the left proper maps as
cofibrations is again a precofibration category. CF1 holds because
isomorphisms are left proper and left proper maps compose; CF3(1) is
stability under pushout; CF3(2) is part (c); CF4 is part (b). -/
theorem leftProperCofibrations_precofibrationCategory [LeftProper C] :
    ABCPrecofibrationCategory (LeftProperCofibrations C) where
  initial_cofibrant := by
    change Cofibration (initial.to (⊥_ (LeftProperCofibrations C)))
    rw [show initial.to (⊥_ (LeftProperCofibrations C)) = 𝟙 _ from
      initialIsInitial.hom_ext _ _]
    exact ⟨isLeftProper_of_isIso (C := C) (𝟙 _)⟩
  cofibrations_comp := ⟨fun _ _ hf hg ↦ IsLeftProper.comp (C := C) hf hg⟩
  weakEquivalence_of_isIso {A B} f _ := by
    have : IsIso (C := C) f := ‹IsIso f›
    exact ⟨(weakEquivalence_of_isIso (C := C) f).mem⟩
  cofibration_of_isIso {A B} f _ _ := by
    have : IsIso (C := C) f := ‹IsIso f›
    exact ⟨isLeftProper_of_isIso (C := C) f⟩
  weakEquivalences_twoOutOfThree :=
    inferInstanceAs (weakEquivalences C).HasTwoOutOfThreeProperty
  hasPushout {A B D} i f _ _ hi := by
    have := hi.mem.hasPushout f
    exact hasPushout_symmetry (C := C) f i
  cofibration_of_isPushout {A B D E i f g j} h _ _ hi :=
    ⟨hi.mem.of_isPushout (C := C) h.flip⟩
  weakEquivalence_of_isPushout {A B D E i f g j} h _ _ hi hw := by
    have : WeakEquivalence (C := C) i := ⟨hw.mem⟩
    exact ⟨(hi.mem.weakEquivalence_of_isPushout (C := C) h.flip).2.mem⟩
  factorization {A B} f _ := by
    obtain ⟨Y, f', r, hf', hr, hfac⟩ := exists_leftProper_factorization (C := C) f
    exact ⟨Y, f', r, ⟨hf'⟩, ⟨hr.mem⟩, hfac⟩

end LeftProperCofibrations

end ABCPrecofibrationCategory

end ABCCofibrations

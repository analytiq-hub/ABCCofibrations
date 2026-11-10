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

end ABCPrecofibrationCategory

end ABCCofibrations

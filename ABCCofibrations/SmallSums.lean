/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Factorization

/-!
# Sums of weak equivalences (Lemmas 1.6.2(1) and 1.6.3(1))

A sum of weak equivalences between cofibrant objects is a weak equivalence,
for finite families under CF1–CF4 and for small families under CF5.
Conversely, given the existence and cofibration clauses CF5(1), the trivial
clause CF5(2) is equivalent to stability of weak equivalences between
cofibrant objects under small sums.

All three statements are instances of one argument, proved once for a fixed
index type: if coproducts of cofibrant families indexed by `ι` exist and
`ι`-indexed sums preserve trivial cofibrations with cofibrant domains, then
they preserve weak equivalences between cofibrant objects. Brown
factorization writes each $f_i$ as $f_i=r_if'_i$ with $f'_i$ a trivial
cofibration and $r_i$ a retraction of a trivial cofibration $s_i$; then
$\coprod f'_i$ and $\coprod s_i$ are weak equivalences, so $\coprod r_i$ is
by two out of three, and hence so is $\coprod f_i$.
-/

public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- The common argument of Lemmas 1.6.2(1) and 1.6.3(1), for a fixed index
type: if sums indexed by `ι` exist for cofibrant families and preserve
trivial cofibrations with cofibrant domains, they preserve all weak
equivalences between cofibrant objects. -/
theorem weakEquivalence_sigmaMap_of_trivialCofibrations {ι : Type w}
    (hex : ∀ X : ι → C, (∀ i, IsCofibrant (X i)) → HasCoproduct X)
    (htriv : ∀ {X Y : ι → C} (g : ∀ i, X i ⟶ Y i) [HasCoproduct X] [HasCoproduct Y],
      (∀ i, IsCofibrant (X i)) → (∀ i, Cofibration (g i)) → (∀ i, WeakEquivalence (g i)) →
        WeakEquivalence (Limits.Sigma.map g))
    {A B : ι → C} (f : ∀ i, A i ⟶ B i) [HasCoproduct A] [HasCoproduct B]
    (hA : ∀ i, IsCofibrant (A i)) (hB : ∀ i, IsCofibrant (B i))
    (hw : ∀ i, WeakEquivalence (f i)) :
    WeakEquivalence (Limits.Sigma.map f) := by
  choose Z j p s hZ hj hp hs hsw hjp hsp using fun i ↦ by
    let := hA i
    let := hB i
    exact exists_brown_factorization (f i)
  let := hex Z hZ
  have hjw (i : ι) : WeakEquivalence (j i) := by
    let := hp i
    let := hw i
    exact weakEquivalence_of_postcomp_of_fac (hjp i)
  have hj' : WeakEquivalence (Limits.Sigma.map j) := htriv j hA hj hjw
  have hs' : WeakEquivalence (Limits.Sigma.map s) := htriv s hB hs hsw
  have hsp' : Limits.Sigma.map s ≫ Limits.Sigma.map p = 𝟙 _ := by
    rw [Limits.Sigma.map_comp_map]
    simp only [hsp, Limits.Sigma.map_id]
  have hp' : WeakEquivalence (Limits.Sigma.map p) := by
    have : WeakEquivalence (𝟙 (∐ B)) := weakEquivalence_of_isIso _
    exact weakEquivalence_of_precomp_of_fac hsp'
  have hjp' : Limits.Sigma.map j ≫ Limits.Sigma.map p = Limits.Sigma.map f := by
    rw [Limits.Sigma.map_comp_map]
    simp only [hjp]
  rw [← hjp']
  infer_instance

/-- Lemma 1.6.2(1), finite case: a finite sum of weak equivalences between
cofibrant objects is a weak equivalence. Only CF1–CF4 are used. -/
theorem weakEquivalence_coproduct_map_finite_of_weakEquivalence
    {ι : Type w} [Finite ι] {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    [HasCoproduct A] [HasCoproduct B]
    (hA : ∀ i, IsCofibrant (A i)) (hB : ∀ i, IsCofibrant (B i))
    (hw : ∀ i, WeakEquivalence (f i)) :
    WeakEquivalence (Limits.Sigma.map f) :=
  weakEquivalence_sigmaMap_of_trivialCofibrations hasCoproduct_finite
    (fun g _ _ hX hg hgw ↦ weakEquivalence_coproduct_map_finite g hX hg hgw) f hA hB hw

end ABCCofibrations.ABCPrecofibrationCategory

namespace ABCCofibrations.ABCCofibrationCategory

open ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]

/-- Lemma 1.6.2(1), small case: under CF5, a small sum of weak equivalences
between cofibrant objects is a weak equivalence. -/
theorem weakEquivalence_coproduct_map_of_weakEquivalence [ABCCofibrationCategory.{w} C]
    {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i) [HasCoproduct A] [HasCoproduct B]
    (hA : ∀ i, IsCofibrant (A i)) (hB : ∀ i, IsCofibrant (B i))
    (hw : ∀ i, WeakEquivalence (f i)) :
    WeakEquivalence (Limits.Sigma.map f) :=
  weakEquivalence_sigmaMap_of_trivialCofibrations hasCoproductOfCofibrant
    (fun g _ _ hX hg hgw ↦ coproduct_weakEquivalence g hX hg hgw) f hA hB hw

/-- Lemma 1.6.3(1), the equivalent formulation of CF5: in a precofibration
category in which coproducts of small cofibrant families exist, CF5(2) for
trivial cofibrations with cofibrant domain is equivalent to stability of
weak equivalences between cofibrant objects under small sums. -/
theorem cf5_trivial_iff [ABCPrecofibrationCategory C]
    (hex : ∀ {ι : Type w} (X : ι → C), (∀ i, IsCofibrant (X i)) → HasCoproduct X) :
    (∀ {ι : Type w} {X Y : ι → C} (g : ∀ i, X i ⟶ Y i) [HasCoproduct X] [HasCoproduct Y],
        (∀ i, IsCofibrant (X i)) → (∀ i, Cofibration (g i)) →
          (∀ i, WeakEquivalence (g i)) → WeakEquivalence (Limits.Sigma.map g)) ↔
      (∀ {ι : Type w} {X Y : ι → C} (g : ∀ i, X i ⟶ Y i) [HasCoproduct X] [HasCoproduct Y],
        (∀ i, IsCofibrant (X i)) → (∀ i, IsCofibrant (Y i)) →
          (∀ i, WeakEquivalence (g i)) → WeakEquivalence (Limits.Sigma.map g)) := by
  constructor
  · intro h ι X Y g _ _ hX hY hw
    exact weakEquivalence_sigmaMap_of_trivialCofibrations (hex (ι := ι))
      (fun g _ _ ↦ h g) g hX hY hw
  · intro h ι X Y g _ _ hX hg hw
    refine h g hX (fun i ↦ ?_) hw
    let := hX i
    let := hg i
    exact cofibrant_target (g i)

end ABCCofibrations.ABCCofibrationCategory

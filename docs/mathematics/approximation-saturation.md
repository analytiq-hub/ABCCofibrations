# Approximation functors, fractions, and saturation (Chapters 5–7)

The implementation is in
[ApproximationTheorem.lean](../../ABCCofibrations/ApproximationTheorem.lean),
[ApproximationExamples.lean](../../ABCCofibrations/ApproximationExamples.lean),
[GabrielZisman.lean](../../ABCCofibrations/GabrielZisman.lean),
[HomotopyIsomorphisms.lean](../../ABCCofibrations/HomotopyIsomorphisms.lean) and
[Saturation.lean](../../ABCCofibrations/Saturation.lean). The source is §5.2–5.5,
§6.1, §6.4 and §7.2 of
[*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4).

## Differences from the paper

* **Category pairs and homotopy categories.** A category pair functor is a
  mathlib `LocalizerMorphism`, with multiplicative classes of weak
  equivalences. The homotopy category is any localization functor; axiom
  LAP2(2) is stated in a chosen localization of the source.
* **The approximation theorem without zig-zags.** The paper builds the
  quasi-inverse of `ho t` on zig-zags and checks six moves. Here a functor
  `M ⥤ ho M'` is built from LAP1 and LAP2(1), sending `f` to `j(f)⁻¹ i(f)`;
  LAP2(2) gives functoriality and Lemma 5.4.2 shows it inverts weak
  equivalences, so it lifts through the localization of `M`. The two natural
  isomorphisms are checked after precomposition with the localization
  functors. Left cleavages (Definition 5.4.3, Lemmas 5.4.5, 5.4.7) are not
  needed and are not formalized.
* **Right approximations** are left approximations of the opposite localizer
  morphism, and their results follow by duality.
* **Theorem 5.2.2** restates mathlib's construction of the localization as a
  quotient of the category of zig-zags.
* **Theorem 6.4.1** derives mathlib's `HasLeftCalculusOfFractions` from the
  paper's hypotheses (b), (c) and restates mathlib's description of maps.
* **Saturation** is stated as: `f` is a weak equivalence iff its image in a
  localization is an isomorphism. CF6 is used through the standalone axioms
  of `SequentialColimits.lean`; the subsequences of even and odd terms are
  compositions with final functors `ℕ ⥤ ℕ`.

## Proofs

**Lemma 5.4.2(1).** If `q ∘ t(g) = p` with `p, q` weak equivalences, LAP2(1)
applied to `(q, p)` gives `k`, `l` with `l ∈ W'` and, by LAP2(2), `g ≫ k = l` in
`ho M'`. So `g` has a right inverse up to `l`; applying the same to `k` shows
`k` has a right inverse too, and `k` is split epi, hence an isomorphism, and
then so is `g`.

**Theorem 5.5.1.** As above; the isomorphism `t ∘ s ≅ 1` uses the formula
`ho t (j⁻¹ i) = p⁻¹ f` for any factorization (from `σ ∘ t(i) = f`,
`σ ∘ t(j) = p`), and `s ∘ t ≅ 1` uses LAP2(2) twice to compare two
factorizations with a common target.

**Corollaries 5.5.3–5.5.4.** If `ho t` is an equivalence, it is faithful, and
the formula above shows that all factorizations of a given pair have the same
image, which is LAP2(2). For a composite, LAP2(1) is obtained by applying
LAP2(1) of each factor in turn, and LAP2(2) from 5.5.3.

**Theorem 6.1.5.** For a cofibrant approximation, LAP1 is CFA4 applied to the
image of the initial object, LAP2(1) is CFA4 applied to a source sum, and
LAP2(2) is Lemma 6.1.4(1).

**Lemma 7.2.1** (Cisinski). A left inverse of `f` in `ho M` is a fraction
`s⁻¹ i` with `i` a cofibration and `s` a trivial cofibration (Theorem
6.4.5(1)); then `i f = s` in `ho M`, so `i f` is left homotopic to `s` and is a
weak equivalence.

**Proposition 7.2.9.** For `p` with the right lifting property against
cofibrations, lift in a square `A → C`, `B → D` built from a cofibrant
replacement and CF4; two out of six in `ho M` makes `p` an isomorphism there.

**Lemma 7.2.2.** Reduce to a cofibration `a : A₀ → A₁` with cofibrant source.
Lemma 7.2.1 gives a sequence of cofibrations with `Aₙ → Aₙ₊₂` trivial; CF6 on
the even and odd subsequences makes `A₀ → colim` and `A₁ → colim` weak
equivalences, so `a` is one.

## Lean correspondence

| Statement | Declaration |
| --- | --- |
| Definition 5.4.1 | `LeftApproximation`, `RightApproximation`, `FactorizationData` |
| Lemma 5.4.2(1), (2) | `LeftApproximation.isIso_map`, `RightApproximation.isIso_map` |
| Theorem 5.5.1 | `LeftApproximation.isLocalizedEquivalence`, `RightApproximation.isLocalizedEquivalence` |
| Corollary 5.5.3(1), (2) | `leftApproximation_iff`, `rightApproximation_iff` |
| Corollary 5.5.4 | `LeftApproximation.comp`, `RightApproximation.comp` |
| Theorem 5.2.2 | `gabrielZisman` |
| Theorem 6.1.5(1), (2) | `IsCofibrantApproximation.leftApproximation`, `IsFibrantApproximation.rightApproximation` |
| Lemma 6.1.3(2) | `IsFibrantApproximation.map_eq_of_map_precomp_eq` |
| Theorem 6.4.1 | `hasLeftCalculusOfFractions_of`, `exists_leftFraction`, `leftFraction_eq_iff`, `map_eq_iff_of_cancel` |
| Lemma 7.2.1(1) | `ABCPrecofibrationCategory.exists_leftInverse_iff`, `ABCPrecofibrationCategory.isIso_map_iff` |
| Lemma 7.2.1(2) | `ABCPrefibrationCategory.exists_rightInverse_iff`, `ABCPrefibrationCategory.isIso_map_iff` |
| Lemma 7.2.2(1), (2) | `ABCPrecofibrationCategory.weakEquivalence_iff_isIso_map`, `ABCPrefibrationCategory.weakEquivalence_iff_isIso_map` |
| Theorem 7.2.3(1), (2) | `ABCCofibrationCategory.weakEquivalence_iff_isIso_map`, `ABCFibrationCategory.weakEquivalence_iff_isIso_map` |
| Proposition 7.2.9(1), (2) | `ABCPrecofibrationCategory.isIso_map_of_hasLiftingProperty`, `ABCPrefibrationCategory.isIso_map_of_hasLiftingProperty` |

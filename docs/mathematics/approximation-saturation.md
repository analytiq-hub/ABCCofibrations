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

## Further results of Chapters 6–7

* **Theorem 7.2.4.** A model category with sequential colimits satisfies CF6
  (lifting classes are stable under transfinite composition), so Lemma 7.2.2
  applies.
* **Theorem 7.2.8(1)** (Cisinski). On the type synonym `Saturated C`, the
  saturation `W̄` with the same cofibrations is a precofibration structure.
  CF3(2): for a cofibration `i` in `W̄`, Lemma 7.2.1 gives cofibrations `i'`,
  `i''` with `i'i`, `i''i'` in `W`; pushing them out along the square gives the
  same for the cobase change `j`, so `j ∈ W̄`. Part (2) is not yet formalized.
* **Lemma 7.2.10.** In a left proper precofibration category, a map with a left
  inverse in `ho M` is followed by a left proper map into a weak equivalence:
  replace `A` cofibrantly, factor, apply Lemma 7.2.1, and push the cofibration
  out along the weak equivalence to `B` (left properness makes the comparison a
  weak equivalence). This is shorter than the paper's construction.
* **Proposition 7.2.11(1), Theorem 7.2.12(1).** `W`-left proper maps are
  `W̄`-left proper, by Lemma 7.2.10 and two out of six in `ho M`; hence the
  saturated structure is left proper. The fibration versions (2) follow in the
  opposite category, using `saturation Cᵒᵖ = (saturation C).op`.
* **Theorem 7.2.8(2).** The saturated prefibration structure lives on the type
  synonym `SaturatedFib C`; it is transported from `Saturated Cᵒᵖ`.
* **Theorem 5.7.1, Corollary 5.7.2.** The paper's total left derived functor
  `(Lu, ε)` is mathlib's `Functor.IsLeftDerivedFunctor` (a right Kan extension,
  in mathlib's terminology). Instead of a regular cleavage, a left
  approximation is shown to be a left derivability structure (Kahn and
  Maltsiniotis; mathlib's `IsLeftDerivabilityStructure.mk'`): LAP2(1) makes the
  categories of resolutions connected and gives resolutions of arrows, and the
  approximation theorem makes `t` a localized equivalence. Mathlib's
  `LocalizerMorphism.Derives` then gives existence (as a pointwise derived
  functor) and the criterion "ε is an isomorphism at every `tA'`". The
  corollary compares any derived functor with `ho(ut) ∘ s` by full faithfulness
  of precomposition with the localization `M' ⥤ ho M'`.
* **Propositions 7.3.2–7.3.3, Corollary 7.3.5.** Maps of `ho M` from a cofibrant
  object to a fibrant model come from maps (via Theorem 6.4.5 and the extension
  property); under BCF6 maps between cofibrant objects do. Local smallness
  follows (`locallySmall_of_surjective`). For model categories, fibrant
  objects are fibrant models.
* **Lemma 7.4.1** is mathlib's fundamental lemma of homotopical algebra.
* **Theorem 7.1.1** is formalized for finite products only (mathlib's
  `Functor.IsLocalization.pi`).
* **Lemma 6.1.4(2)** follows from 6.1.4(1) in the opposite category via
  mathlib's `RightFraction.op_map`.

| Statement | Declaration |
| --- | --- |
| Theorem 7.1.1, finite | `isLocalization_pi` |
| Theorem 7.2.4 | `QuillenModelCategory.weakEquivalence_iff_isIso_map` |
| Theorem 5.7.1(1), (2) | `LeftApproximation.hasLeftDerivedFunctor`, `LeftApproximation.isLeftDerivedFunctor_iff`, `RightApproximation.hasRightDerivedFunctor`, `RightApproximation.isRightDerivedFunctor_iff` |
| Theorem 5.8.1, adjunction part | `derived_adjunction` |
| Corollary 5.7.2(1), (2) | `LeftApproximation.leftDerivedFunctor_iso`, `RightApproximation.rightDerivedFunctor_iso` |
| Theorem 7.2.8(1) | `ABCPrecofibrationCategory.saturated_precofibrationCategory`, `saturation`, `Saturated` |
| Theorem 7.2.8(2) | `ABCPrefibrationCategory.saturated_prefibrationCategory`, `SaturatedFib`, `saturation_op` |
| Lemma 7.2.10(1), (2) | `exists_leftInverse_iff_leftProper`, `isIso_map_iff_leftProper`, `exists_rightInverse_iff_rightProper`, `isIso_map_iff_rightProper` |
| Proposition 7.2.11(1), (2) | `isLeftProper_saturated`, `isRightProper_saturated` |
| Theorem 7.2.12(1), (2) | `saturated_leftProper`, `saturated_rightProper` |
| Definition 7.3.1 | `IsFibrantModel`, `IsCofibrantModel` |
| Proposition 7.3.2(1), (2) | `map_surjective_of_isFibrantModel`, `map_surjective_of_isCofibrantModel` |
| Proposition 7.3.3(1), (2) | `locallySmall_of_fibrantModels`, `locallySmall_of_cofibrantModels` |
| Proposition 7.3.4(1), (2) | `map_surjective_of_bauesAxiom`, `map_eq_iff_leftHomotopy` |
| Corollary 7.3.5 | `locallySmall_of_bauesAxiom`, `locallySmall_of_trivialCofibration_lifting`, `locallySmall_of_cofibration_lifting`, `QuillenModelCategory.locallySmall_homotopyCategory` |
| Lemma 7.4.1 | `QuillenModelCategory.quillen_homotopy_tfae` |
| Lemma 6.1.4(2) | `IsFibrantApproximation.rightFraction_map_eq_of_ambient_comparison` |

## Chapter 8: relative colimits, cofinality, Grothendieck construction

These classical results are restated from mathlib in
[DiagramColimits.lean](../../ABCCofibrations/DiagramColimits.lean). The paper's
relative colimit `colim^u` is mathlib's (pointwise) left Kan extension; a right
cofinal functor is mathlib's `Functor.Final`, a left cofinal one `Functor.Initial`.

| Statement | Declaration |
| --- | --- |
| Lemma 8.2.1(1), (2) | `hasLeftKanExtension_of_hasColimit_comma`, `hasRightKanExtension_of_hasLimit_comma` |
| Lemma 8.2.2(1), (2) | `leftKanExtension_comp`, `rightKanExtension_comp` |
| Proposition 8.5.3(1) | `final_iff_isIso_colimit_pre` (small categories; cocomplete targets in universe `v + 1`) |
| Proposition 8.5.4(1), (2) | `final_hasColimit_iff`, `initial_hasLimit_iff` |
| Proposition 8.6.2(1) | `grothendieck_colimit` (with mathlib's hypothesis on the transition functors) |
| Corollary 8.6.3(1), (2) | `colimit_prod`, `limit_prod` (mathlib's Fubini needs `HasColimitsOfShape K M`) |

| Lemma 8.5.2 | `adjunction_cofinal` (terminal objects of the comma categories stand in for contractible nerves) |
| Proposition 8.5.3(2) | `initial_iff_isIso_limit_pre` |
| Proposition 8.6.1(1), (2) | `fiberInclusion_isRightAdjoint`, `fiberInclusionContra_isLeftAdjoint` |
| Proposition 8.6.2(2) | `grothendieck_limit` |

## Chapter 9

| Statement | Declaration |
| --- | --- |
| Lemma 9.3.3 | `cofibration_comparison_comp`, `weakEquivalence_comparison_comp` (both namespaces) |
| Lemma 9.3.4(1), (2) | `cofibration_sequence_comparison`, `weakEquivalence_sequence_comparison`, `ABCFibrationCategory.fibration_sequence_comparison`, `ABCFibrationCategory.weakEquivalence_sequence_comparison` |
| Definitions 9.1.1–9.1.3, 9.2.2 | `IsDirect`, `IsInverse`, `LatchingCategory`, `latchingObj`, `latchingMap`, `IsReedyCofibrant`, `IsReedyCofibration`, `IsReedyFibrant`, `IsReedyFibration` |
| Proposition 9.2.3(1), (2) | `IsReedyCofibration.comp`, `isReedyCofibration_of_isIso`, `IsReedyFibration.comp`, `isReedyFibration_of_isIso` |
| Lemma 9.3.1(1) | `colimit_isPushout_latching` |
| Theorem 9.3.5(1)(a), finite direct categories | `reedyCofibrant_colimit_finite` |
| Theorem 9.3.5(1)(b), (c), finite direct small categories | `reedyCofibration_colimMap`, `reedyCofibrant_colimMap_weakEquivalence` |
| Corollary 9.3.6(1), finite direct small categories | `IsReedyCofibration.cofibration_app` |
| Definition 9.7.1, Lemma 9.7.2 | `LeftExact`, `RightExact`, `LeftExact.comp`, `LeftExact.weakEquivalence_map`, `RightExact.comp`, `RightExact.weakEquivalence_map` |

Theorem 9.3.5 is proved for direct categories with finitely many objects (and,
for (b), (c), finitely many morphisms), by induction on a degree bound and on the
number of objects: an object `d` of maximal degree has no non-identity maps out
of it, `colim_D X` is the pushout of Lemma 9.3.1, and the gluing lemma applies.
The restrictions of Reedy data to `D ∖ {d}` and to latching categories (the
paper's identification (9.1.2) of iterated latching categories) are transferred
along final functors (`ReedyTransfer.lean`). The paper's general small case,
which needs CF5 for the infinitely many objects of a degree and CF6 for the
infinitely many degrees, is not yet formalized.

Latching objects are colimits whose existence is recorded as instance
hypotheses; matching objects and Reedy fibrations are defined through the
opposite categories. In Lemma 9.3.4(1)(a) and 9.3.4(2)(a) the paper's
cofibration (resp. fibration) hypothesis on the second sequence is not needed.
Definition 9.7.1 asks preservation of colimits of all transfinite sequences of
cofibrations, not only continuous ones.

## Chapter 7, weak saturation

Theorem 7.2.7 (`weakSaturation_tfae`, both namespaces). The paper's step
"weakly saturated ⟹ saturated" applies Lemma 7.2.1 in an over category without
justifying the needed left inverse; the formalization argues directly in `M`
(see the module docstring of `WeakSaturation.lean`).

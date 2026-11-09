# Shared localization transfer lemmas

The implementation is
[LocalizationTransfer.lean](../../ABCCofibrations/LocalizationTransfer.lean).
It contains the purely categorical steps that the cofibration and fibration
theories previously proved twice. No cofibrations, fibrations, cylinders,
path objects, or ABC axioms appear in this module.

## Differences from the paper

The paper does not isolate these statements. They are the formal content of
two routine steps used in Chapter 6: "a functor which identifies homotopic
maps factors through the homotopy category" and "inverting the trivial
(co)fibrations is the same as inverting all weak equivalences". The
formalization proves each step once, for arbitrary categories and morphism
classes, and the cofibrant and fibrant comparisons are instances. This is a
change of proof organization only; no statement of the paper is changed and
no hypothesis is added.

## Factorizations through a quotient

Let $\mathcal A$ be a category, $\sim$ a relation on its arrows, $W$ a class of
morphisms of $\mathcal A$ and $W'$ a class of morphisms of the quotient
$\mathcal A/{\sim}$ with

$$
W=\pi^{-1}(W'),\qquad \pi:\mathcal A\to\mathcal A/{\sim}.
$$

Suppose $\gamma:\mathcal A\to\mathcal A[W^{-1}]$ factors as
$\gamma=\pi\,\bar\gamma$ (a strict equality of functors). Then $\bar\gamma$
inverts $W'$, since $\pi$ is full and bijective on objects, and $\bar\gamma$
has the strict universal property of the localization of
$\mathcal A/{\sim}$ at $W'$: a $W'$-inverting functor $G$ lifts through
$\mathcal A[W^{-1}]$ as the lift of $\pi G$, and uniqueness follows from the
universal properties of the quotient and of $\gamma$. Hence $\bar\gamma$ is a
localization functor.

Mathlib's `HomRel.FactorsThroughLocalization` proves the companion statement:
$\pi$ composed with a localization of the quotient is a localization of
$\mathcal A$. We still use it to show that $\pi$ induces an equivalence of
localizations. It does not directly provide the strict universal property of
$\bar\gamma$, which is why the shared lemma is needed.

Instances: the left-homotopy quotient of cofibrant objects
(`leftHomotopyComparisonStrictUniversalProperty`) and the native
right-homotopy quotient of fibrant objects
(`rightHomotopyComparisonStrictUniversalProperty`).

## Classes with the same inverting functors

Let $W_1,W_2$ be classes of morphisms of $\mathcal A$ such that the canonical
localization functor $\gamma_2$ inverts $W_1$ and $\gamma_1$ inverts $W_2$.
Every functor $F$ inverting $W_2$ is $\gamma_2$ followed by its lift, so $F$
inverts $W_1$; symmetrically. Hence $\gamma_1$ has the strict universal
property for $W_2$, and every localization functor at $W_1$ is a
localization functor at $W_2$.

Instances: Brown's lemma shows that on cofibrant objects the trivial
cofibrations and the weak equivalences have the same inverting functors,
and dually on fibrant objects for trivial fibrations. The canonical
comparison equivalences and their compatibility isomorphisms with the
localization functors (`trivialCofibrationLocalizationEquivalence_fac`,
`trivialFibrationLocalizationEquivalence_fac`) are unchanged.

## Lean correspondence

All names are in `CategoryTheory.Localization`.

| Statement | Declaration |
| --- | --- |
| The quotient factorization inverts $W'$ | `quotientLift_inverts` |
| Its strict universal property | `strictUniversalPropertyFixedTargetQuotientLift` |
| It is a localization at $W'$ | `isLocalization_quotientLift` |
| Inverting $W_2$ implies inverting $W_1$ | `isInvertedBy_of_isInvertedBy_Q` |
| Strict universal property of $\gamma_1$ for $W_2$ | `strictUniversalPropertyFixedTargetQOfIsInvertedBy` |
| Localizations at $W_1$ are localizations at $W_2$ | `isLocalization_of_isInvertedBy_Q` |

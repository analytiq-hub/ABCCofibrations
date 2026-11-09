# Absolute derived functors and Quillen adjunctions

The implementations are [DerivedAbsoluteness.lean](../../ABCCofibrations/DerivedAbsoluteness.lean)
and [QuillenAdjunction.lean](../../ABCCofibrations/QuillenAdjunction.lean).

## Differences from the paper

We keep the hypotheses of Definition 6.2.4(1)–(3) and Theorem 6.2.5(1):
a cofibrant approximation $t_C:\mathcal C'\to\mathcal C$, a fibrant
approximation $t_D:\mathcal D'\to\mathcal D$, and an adjunction
$G:\mathcal C\rightleftarrows\mathcal D:F$, such that $Gt_C$ sends trivial
cofibrations to weak equivalences and $Ft_D$ sends trivial fibrations to
weak equivalences. We require only CF1–CF4 on the cofibration side and
F1–F4 on the fibration side. No category is assumed to be a model category
or to carry both structures.

The paper derives its result from the Chapter 5 approximation/adjunction
theory. Following the user's preference for a simpler approach where
available, we instead use mathlib's implementation of Maltsiniotis's
[*Quillen's adjunction theorem for derived functors, revisited*](https://arxiv.org/abs/math/0611952v1).
We prove that the relevant derived functors are preserved by arbitrary
postcomposition, then apply `CategoryTheory.Adjunction.derived`. We do not
assume absoluteness as an extra hypothesis. This changes the proof route,
not the Quillen-pair hypotheses or the conclusion.

`IsQuillenAdjunction tC tD adj` is a proposition recording the two preservation
conditions. The adjunction and approximation structures are supplied as
parameters, rather than being stored again in the class. The Quillen
equivalence condition of Definition 6.2.4(4) is recorded separately in
`IsQuillenEquivalence`; results use it together with `IsQuillenAdjunction`.
The construction works for any chosen total derived functors and any
source and target localizations, and we also prove their joint existence.

## Why arbitrary postcomposition preserves these derived functors

Let $\Phi$ be a left derivability structure, and suppose $\Phi$ followed by
$U$ inverts source weak equivalences. Mathlib's criterion says that a functor
with counit is left derived precisely when the counit is invertible at
every object in the image of $\Phi$.

For any functor $K$, the composite $K\circ U$ still inverts those weak equivalences.
The whiskered counit has components $K(\epsilon_X)$, which remain
invertible. The criterion therefore proves that postcomposing any left
derived functor by $K$ preserves its derived universal property. The same
argument applies to right derived functors and their units. This is
absoluteness; we prove it for general derivability structures, so the result
can be reused outside cofibration categories.

The explicit associators in Lean account for the parenthesization of the
composed functors; they have identity components and add no assumption.

## The derived adjunction

Write $L_C$ and $L_D$ for the localization functors. Given total derived
functors with comparison maps

$$
\epsilon:L_C\,\mathbf L G\longrightarrow G L_D,
\qquad
\eta:F L_C\longrightarrow L_D\,\mathbf R F,
$$

these displayed composites use diagrammatic order, as does Lean's `⋙`.
Brown's lemma after localization shows that $t_C G L_D$ and $t_D F L_C$
invert source weak equivalences. Thus the two approximation derivability
structures supply absoluteness. In particular, postcomposition by
$\mathbf R F$ preserves the left derived functor, and postcomposition by
$\mathbf L G$ preserves the right derived functor. These are the two
hypotheses required by `Adjunction.derived`, giving

$$
\mathbf L G\dashv\mathbf R F.
$$

Mathlib constructs the derived unit and counit from the original unit and
counit using the derived universal properties, and proves the triangle
identities. Our proof reuses that construction rather than duplicating it.

## Lean correspondence and status

All names below are in `ABCCofibrations`.

| Statement | Declaration |
| --- | --- |
| Arbitrary postcomposition preserves a left derived functor | `isLeftDerivedFunctor_postcomp_of_derives` |
| Arbitrary postcomposition preserves a right derived functor | `isRightDerivedFunctor_postcomp_of_derives` |
| Definition 6.2.4(1)–(3) | `IsQuillenAdjunction` |
| Theorem 6.2.5(1), for arbitrary derived choices | `quillenDerivedAdjunction` |
| Joint existence of derived functors and an adjunction | `exists_quillenDerivedAdjunction` |

## Comparison formulas, full faithfulness, and Quillen equivalence

[QuillenComparison.lean](../../ABCCofibrations/QuillenComparison.lean)
exposes the comparison equations for the derived unit and counit. It also
proves compatibility of localized adjoint arrows with the derived
hom-set adjunction. For $f:G(X)\to Y$, this equation is, in diagrammatic
composition order,

$$
\operatorname{adj}_{der}(\epsilon_X\,L_D(f))
  =L_C(\operatorname{adj}(f))\,\eta_Y.
$$

There is a companion equation in the opposite direction. These hold for
arbitrary $X,Y$, without cofibrancy or fibrancy assumptions on them.

For condition (4l), suppose a weak equivalence
$f:G(t_C A)\to t_D B$ always has a weak-equivalence adjoint.
Choose a right resolution $G(t_C A)\xrightarrow{\sim}t_D B$.
The comparison equation and invertibility of the derived counit and unit
on approximation image objects show that the derived adjunction unit is
invertible at $L_C(t_C A)$. These objects cover the source localization up
to isomorphism, so the whole unit is invertible. The derived left adjoint
is therefore fully faithful.

Dually, under (4r), a weak-equivalence adjoint implies that the original
arrow is a weak equivalence. Choose a left resolution
$t_C A\xrightarrow{\sim}F(t_D B)$ and apply the companion equation.
The derived counit becomes invertible, and the derived right adjoint is
fully faithful. These prove both parts of Theorem 6.2.5(2).

The condition of Definition 6.2.4(4) combines both implications. Thus the
derived unit and counit are invertible and the derived adjunction yields
an equivalence with the chosen derived functors as forward and inverse
functors. This proves Theorem 6.2.5(3).

**Differences from the paper:** the paper deduces 6.2.5(2)–(3) from the
abstract theorem 5.8.1. We prove the one-sided criteria directly from the
comparison equations for the Maltsiniotis-derived adjunction. The proof
uses exactly the implications (4l) and (4r), respectively, and inverts
weak equivalences after localization; it does not assume that isomorphisms
in the localization reflect to ambient weak equivalences. Mathlib's
`Adjunction.toEquivalence` supplies the resulting equivalence structure.
The separate class for condition (4) avoids duplicating the Quillen-pair
preservation conditions. No additional hypotheses are imposed.

| Statement | Declaration in `ABCCofibrations` |
| --- | --- |
| Derived unit and counit equations | `quillenDerivedAdjunction_unit_fac_app`, `quillenDerivedAdjunction_counit_fac_app` |
| Localized adjoint-arrow equations | `quillenDerivedAdjunction_homEquiv`, `quillenDerivedAdjunction_homEquiv_symm` |
| (4l) makes the derived unit invertible | `isIso_quillenDerivedUnit_of_map_weakEquivalence` |
| Left full faithfulness | `fullyFaithful_quillenLeftDerived_of_map_weakEquivalence` |
| (4r) makes the derived counit invertible | `isIso_quillenDerivedCounit_of_adjoint_weakEquivalence` |
| Right full faithfulness | `fullyFaithful_quillenRightDerived_of_adjoint_weakEquivalence` |
| Definition 6.2.4(4) | `IsQuillenEquivalence` |
| Theorem 6.2.5(3) | `quillenDerivedEquivalence` |
| The individual functors are equivalences | `isEquivalence_quillenLeftDerived`, `isEquivalence_quillenRightDerived` |

Theorem 6.2.5(1)–(3) is now proved for arbitrary choices of localizations
and derived functors. Joint derived existence is supplied by
`exists_quillenDerivedAdjunction` from the preceding module.

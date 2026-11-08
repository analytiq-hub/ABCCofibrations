# Total left derived functors

This note covers Theorem 6.2.1(1) of Rădulescu-Banu's
[*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4).
The Lean implementation is [DerivedFunctor.lean](../../ABCCofibrations/DerivedFunctor.lean).
It requires CF1–CF4 and the
[comparison with cofibrant-object localization](../cofibrant-replacements.md).

## Differences from the paper

The final existence statement has the hypotheses of Theorem 6.2.1(1), with
the source and target localization functors explicit. The paper proves this
through general cofibrant approximation functors and its Chapter 5 approximation
theory. We specialize to inclusion of cofibrant objects, then use mathlib's
left derivability structures, based on Kahn–Maltsiniotis, to supply the
universal property. General cofibrant approximations, Theorem 6.2.2(1), and
the dual right-derived theory have not been formalized here.

The general intermediate theorem takes a functor into any category that
inverts trivial cofibrations between cofibrant objects. Mathlib supplies a
**pointwise** left derived functor, and we retain that stronger existence
result. The total-derived statement applies this to the original functor
followed by target localization; no target model structure, two-out-of-three
axiom, or chosen saturation is assumed.

There is a terminology issue to make explicit. Definition 5.6.1 in the paper
calls the total left derived functor a “left Kan extension.” The proof of
Theorem 5.7.1 specifies a transformation from the derived composite to the
original localized functor and a **terminal** universal property. Mathlib calls
that precise property a **right Kan extension**, while still naming the result
a left derived functor. The formalization uses the transformation direction
and terminal property spelled out below, matching that proof in the paper.

## Statement and universal property

Let $\mathcal M$ be a precofibration category, let $(\mathcal N,W_{\mathcal N})$
be a category with a designated class of weak equivalences, and let
$u:\mathcal M\to\mathcal N$ send trivial cofibrations between cofibrant
objects to weak equivalences. Given localization functors
$\gamma_{\mathcal M}$ and $\gamma_{\mathcal N}$, there exist

$$
\mathbf L u:\mathcal M[W^{-1}]\longrightarrow\mathcal N[W_{\mathcal N}^{-1}],
\qquad
\varepsilon:(\mathbf L u)\circ\gamma_{\mathcal M}
\Longrightarrow\gamma_{\mathcal N}\circ u.
$$

For every functor $G$ with the same source and target as $\mathbf L u$ and
every natural transformation
$\alpha:G\circ\gamma_{\mathcal M}\Rightarrow\gamma_{\mathcal N}\circ u$,
there is a unique $\tau:G\Rightarrow\mathbf L u$ such that

$$
\varepsilon\circ(\tau\gamma_{\mathcal M})=\alpha.
$$

Moreover, $\varepsilon_A$ is invertible whenever $A$ is cofibrant. In Lean,
composition is written left to right: `L ⋙ LF ⟶ F ⋙ R` represents
$\varepsilon$, and `LF.IsLeftDerivedFunctor ε (weakEquivalences C)` asserts
the universal property. The theorem returns this proof along with `LF` and
`ε`; it does not merely produce a candidate functor.

## Proof structure

The inclusion $\mathcal M_{\mathrm{cof}}\hookrightarrow\mathcal M$ is a
left derivability structure by mathlib's constructor. Its hypotheses are
already proved: it is a localized equivalence, each category of cofibrant
replacements is connected, and every ambient arrow has a replacement square.
Weak equivalences contain identities by CF1.

Set $F=\gamma_{\mathcal N}\circ u$. The assumed preservation property
makes $F$ invert trivial cofibrations between cofibrant objects. Brown's
functor lemma then makes its restriction invert all weak equivalences.
This restriction has a pointwise left derived functor given by localization.
The derivability structure transfers existence to $F$ on the ambient category.

For the counit property, the derived functor of the restriction has invertible
counit because it inverts weak equivalences. Mathlib's comparison theorem for
left derivability structures transfers invertibility to the ambient counit
at every cofibrant object. This argument applies to any left derived functor
with the stated universal property, not just a particular chosen construction.

## Lean correspondence and status

| Mathematical result | Declaration |
| --- | --- |
| Cofibrant inclusion is a left derivability structure | `cofibrantInclusion_isLeftDerivabilityStructure` |
| Pointwise existence for an inverting functor | `hasPointwiseLeftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations` |
| Any derived counit is invertible at cofibrant objects | `isIso_leftDerivedCounit_app_cofibrant` |
| Existence with universal property and counit statement | `exists_leftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations` |
| Theorem 6.2.1(1), with target localization | `exists_totalLeftDerivedFunctor_of_map_trivialCofibrations` |

All these results are proved. Derived equivalences, Quillen adjunctions,
general cofibrant approximation functors, and the dual fibration-side results
remain outside this increment. This note was reviewed against the accompanying
Lean source following commit `80d16e2`.

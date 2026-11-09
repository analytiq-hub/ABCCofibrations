# Prefibration categories through opposite categories

The implementation is [FibrationBasic.lean](../../ABCCofibrations/FibrationBasic.lean).
It starts the dual theory needed for the fibration-side results of Chapter 6.

## Differences from the paper

The paper states prefibration axioms F1–F4 alongside the dual cofibration
axioms. We define `ABCCofibrations.ABCPrefibrationCategory C` as an
abbreviation for `ABCPrecofibrationCategory Cᵒᵖ`. Mathlib already defines
cofibrations on the opposite as the opposites of the supplied fibrations,
and similarly transports weak equivalences. A terminal object is supplied
by `[HasTerminal C]`, which gives an initial object in the opposite.
Thus these are precisely the dual axioms, with no extra lifting, model
category, or completeness assumption. Only F1–F4 are included; F5–F6 and
the full prefibration-to-fibration extension are not implemented here.

This changes the implementation organization: the dual axioms and proofs
are reused rather than maintained as a second independent class with
separate proofs. We provide theorems stated directly in the original
category so users need not manipulate opposite arrows for basic work.
The abbreviation is usable as a typeclass hypothesis; it introduces no
new Lean axioms.

## Objects and the choice of terminal object

Fibrancy of $A$ means that $A\to\top$ is a fibration. In the opposite,
cofibrancy of $A^{op}$ means that $\bot\to A^{op}$ is a cofibration.
The chosen $\bot$ need not be definitionally the chosen $\top^{op}$.
We compare them by their unique initial-object isomorphism, and use CF1
and closure of cofibrations under composition to transport the condition.
This proves

$$
A\text{ fibrant in }\mathcal C
\quad\Longleftrightarrow\quad
A^{op}\text{ cofibrant in }\mathcal C^{op}.
$$

In particular the terminal object is fibrant, and a fibration with fibrant
target has fibrant source.

## Basic consequences

Fibrations compose, weak equivalences satisfy two out of three, and
isomorphisms are weak equivalences. An isomorphism with fibrant target
is a fibration. F4 provides, for any $f:A\to B$ with $B$ fibrant,

$$
A\xrightarrow[\sim]{w}Z\xrightarrow{p}B,
\qquad p\text{ a fibration},\qquad pw=f.
$$

Every object has a fibrant replacement $A\xrightarrow{\sim}R$.
No functorial choices are required.

For a fibration $p:A\to B$ and a map $f:D\to B$, with $B,D$ fibrant,
the pullback exists. Its projection to $D$ is a fibration, and is a weak
equivalence if $p$ is. These are exactly the restricted F3 hypotheses;
we do not assume all pullbacks exist or preserve weak equivalences.

All these statements are obtained from the corresponding CF1–CF4 facts
on the opposite category.

## Lean correspondence and remaining work

All names except the abbreviation are in
`ABCCofibrations.ABCPrefibrationCategory`.

| Statement | Declaration |
| --- | --- |
| F1–F4 by duality | `ABCCofibrations.ABCPrefibrationCategory` |
| Fibrant iff opposite cofibrant | `isFibrant_iff_isCofibrant_op` |
| Fibrancy supplies opposite cofibrancy | `isCofibrant_op` |
| Terminal object is fibrant | `terminal_fibrant` |
| Composition and two out of three | `fibrations_comp`, `weakEquivalences_twoOutOfThree` |
| Isomorphisms | `weakEquivalence_of_isIso`, `fibration_of_isIso` |
| Fibrancy of a fibration's source | `fibrant_source` |
| Fibrant replacement | `exists_fibrant_replacement` |
| F4 factorization | `factorization` |
| Restricted pullbacks | `hasPullback` |
| Base change | `fibration_of_isPullback`, `weakEquivalence_of_isPullback` |

## Fibrant approximations and right-derived existence

[FibrantApproximation.lean](../../ABCCofibrations/FibrantApproximation.lean)
defines `ABCCofibrations.IsFibrantApproximation F` as
`IsCofibrantApproximation F.op`, the dual of Definition 6.1.1 and the
paper's Definition 6.1.2. Every source and image object is fibrant.
Fibrations are preserved and weak equivalences are detected exactly.
Pullbacks of two fibrations are preserved. An ambient map into an image
admits the dual factorization

$$
B\xrightarrow[\sim]{w}t(Z)\xrightarrow{t(p)}t(A),
\qquad p\text{ a source fibration}.
$$

The localization equivalence for the opposite approximation gives a
localization equivalence in the original direction, Theorem 6.1.7(2).
Mathlib's duality for derivability structures then gives a right derivability
structure. We do not reconstruct resolution-fraction arguments a second time.

For $u:\mathcal M\to\mathcal N$ and a fibrant approximation
$t:\mathcal M'\to\mathcal M$, suppose $ut$ sends trivial fibrations
to weak equivalences. After target localization $R$, Brown's lemma on the
opposite category shows that $Rut$ inverts all source weak equivalences.
The right derivability structure supplies a pointwise total right derived
functor of $u$. Any derived unit is invertible at every $t(A)$.
The result allows arbitrary source and target localizations.

**Differences from the paper:** the fibrant approximation definition and the
localization-equivalence proof are implemented through opposites, using the
already proved cofibrant theory. Right-derived existence uses mathlib's
right derivability machinery after this transport. We apply Brown's lemma
to isomorphisms after target localization, without assuming saturation or
two out of three for the original target weak equivalences. The v4 displayed
hypothesis in Theorem 6.2.2(2) asks that $u$ send trivial fibrations to weak
equivalences; we use the weaker composite condition on $ut$, matching the
dual of (1). The displayed hypothesis implies ours because $t$ preserves
trivial fibrations. The unit points from the localized original functor to the derived functor
composed with source localization.

The following names are in `ABCCofibrations.IsFibrantApproximation`:

| Statement | Declaration |
| --- | --- |
| Source and image fibrancy | `source_fibrant`, `obj_fibrant` |
| Preservation and detection | `map_fibration`, `weakEquivalence_map_iff` |
| Pullback preservation | `map_isPullback` |
| Dual factorization | `factorization` |
| Localizer morphism and equivalence | `toLocalizerMorphism`, `toLocalizerMorphism_isLocalizedEquivalence` |
| Right derivability structure | `toLocalizerMorphism_isRightDerivabilityStructure` |
| Pointwise right-derived existence | `hasPointwiseRightDerivedFunctor_of_inverts_trivialFibrations` |
| Any derived unit on an image object is invertible | `isIso_rightDerivedUnit_app` |
| Total right-derived existence | `exists_totalRightDerivedFunctor_of_map_trivialFibrations` |

The native fibrant-subcategory instances, Theorems 6.2.1(2) and 6.2.3(2),
and Quillen adjunctions remain to be implemented. Mathlib's
`CategoryTheory.Functor.Derived.Adjunction` already implements the
Maltsiniotis argument for absolute derived functors: it requires that the
relevant composites remain derived functors. Before applying it we must
supply those preservation statements. Its availability does not itself
prove these hypotheses for our categories.

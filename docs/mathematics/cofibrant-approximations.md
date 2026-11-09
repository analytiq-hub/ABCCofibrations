# Cofibrant approximation functors

This note accompanies [CofibrantApproximation.lean](../../ABCCofibrations/CofibrantApproximation.lean)
and Definition 6.1.1 of Rădulescu-Banu's
[*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4).

## Differences from the paper and proof strategy

The definition keeps CFA1–CFA4 and the paper's requirement that source and
target are precofibration categories, with every source object cofibrant.
We store the all-cofibrant condition as a field of
`ABCCofibrations.IsCofibrantApproximation F`. The existing ABC and mathlib
morphism classes are supplied separately; this introduces no new notion of
cofibration or weak equivalence.

CFA1 uses mathlib's preservation of the empty colimit to express preservation
of the initial object. CFA3 is expressed by preservation of a pushout square
of two cofibrations, rather than invertibility of the canonical comparison
map. These are equivalent formulations. We do not strengthen CFA3 to
arbitrary pushouts, and CFA4 asserts only existence, without a functorial
choice of factorization. No localized-equivalence hypothesis is included.

Our interface uses mathlib's localizer and resolution categories to prepare
for the Kahn–Maltsiniotis derivability machinery used earlier. This changes
the proof organization, not the CFA axioms. Mathlib's available derivability
constructor assumes a localized equivalence in addition to connected
resolutions and arrow resolutions. Thus the resolution results below do
**not** by themselves prove the missing localization equivalence.

Maltsiniotis's
[*Quillen's adjunction theorem for derived functors, revisited*](https://arxiv.org/abs/math/0611952v1)
gives a formal adjunction argument using absolute derived functors without
their explicit construction. That offers a route to inspect before the later
adjunction work. We have not claimed it proves the current CFA localization
bridge, or established the required absoluteness statements yet.

## Axioms

Let $t:\mathcal M'\to\mathcal M$ be a functor between precofibration
categories, with every object of $\mathcal M'$ cofibrant.

| Axiom | Requirement |
| --- | --- |
| CFA1 | $t$ preserves the initial object and cofibrations. |
| CFA2 | $f$ is a weak equivalence exactly when $t(f)$ is. |
| CFA3 | $t$ preserves pushouts of spans whose two maps are cofibrations. |
| CFA4 | Every $f:t(A)\to B$ factors as $t(A)\xrightarrow{t(i)}t(Z)\xrightarrow{p}B$, with $i$ a cofibration and $p$ a weak equivalence. |

## Elementary consequences and resolutions

Every $t(A)$ is cofibrant: apply $t$ to the cofibration $\varnothing\to A$
and use preservation of the initial object. CFA1 and CFA2 imply preservation
of trivial cofibrations. CFA2 also makes $t$ a morphism of localizers whose
source weak-equivalence class is exactly the inverse image of the target class.

For any $B\in\mathcal M$, apply CFA4 to the unique map $t(\varnothing)\to B$.
The resulting $p:t(Z)\xrightarrow{\sim}B$ is a left resolution in mathlib's
terminology. Given an ambient arrow $f:B\to C$ and a resolution $p:t(A)\to B$,
apply CFA4 to $fp$. This supplies a commutative resolution square with both
vertical maps weak equivalences. Every ambient arrow therefore has a resolution.

Two resolutions $p:t(A)\xrightarrow{\sim}X$ and
$q:t(B)\xrightarrow{\sim}X$ have a common extension. Form the source pushout
$P=A\amalg_{\varnothing}B$. Both maps from the initial object are cofibrations,
so CFA3 preserves this pushout. Initiality of $t(\varnothing)$ and the pushout
property give $u:t(P)\to X$ restricting to $p$ and $q$.
Apply CFA4 to obtain

$$
t(P)\xrightarrow{t(k)}t(Z)\xrightarrow[\sim]{r}X.
$$

The composites $i:A\to P\to Z$ and $j:B\to P\to Z$ are cofibrations.
Their images satisfy $rt(i)=p$, $rt(j)=q$. Two out of three makes their
images weak equivalences, and CFA2 reflects this to $i$ and $j$. Thus

$$
(A,p)\longrightarrow(Z,r)\longleftarrow(B,q)
$$

is a zigzag in the category of resolutions, proving that category connected.

## Homotopy cancellation: Lemma 6.1.2(1)

Suppose $f,g:A\to B$ in $\mathcal M'$ and an ambient weak equivalence
$b:t(B)\to X$ satisfy $b\,t(f)=b\,t(g)$. Then $f$ and $g$ are left
homotopic in $\mathcal M'$.

The construction follows the paper. First factor the full boundary
$[f,g]:A\amalg A\to B$ as a cofibration followed by a weak equivalence.
It suffices to handle the resulting pair: CFA2 preserves that weak
equivalence, and postcomposition preserves left homotopy.

When $[f,g]$ is a cofibration, choose a good cylinder $IA$ and form
$P=B\amalg_{A\amalg A}IA$. Both maps in the defining span are
cofibrations, so CFA3 preserves this pushout. The equality in the hypothesis
gives a map $u:t(P)\to X$. Apply CFA4 to factor it as

$$
t(P)\xrightarrow{t(j)}t(Z)\xrightarrow[\sim]{p}X.
$$

The composite $q:B\to P\to Z$ is a cofibration and satisfies
$p\,t(q)=b$. Two out of three and CFA2 make $q$ a weak equivalence.
The map $IA\to P\to Z$ is a cylinder homotopy from $qf$ to $qg$,
which exhibits the required left homotopy.

**Difference from the paper:** the paper concludes equality in the localized
category. The Lean theorem records the explicit, stronger left-homotopy
witness produced by this same construction. It chooses a good cylinder to
match our left-homotopy interface. The ambient object $X$ need not be
cofibrant, and no stronger pushout-preservation axiom is used. The proof is in
[CofibrantApproximationHomotopy.lean](../../ABCCofibrations/CofibrantApproximationHomotopy.lean).

## Independence of fractions: Lemma 6.1.3(1)

Consider two source fractions
$A\xrightarrow{i'}D'\xleftarrow[\sim]{j'}B$ and
$A\xrightarrow{i''}D''\xleftarrow[\sim]{j''}B$.
Suppose ambient weak equivalences $p:t(D')\to X$ and
$q:t(D'')\to X$ satisfy

$$
p\,t(i')=q\,t(i''),\qquad p\,t(j')=q\,t(j'').
$$

Then the two fractions have the same value under every functor $G$ that
inverts source weak equivalences, hence in the source localization.

Take a common resolution extension $a:D'\to Z$, $c:D''\to Z$,
$r:t(Z)\xrightarrow{\sim}X$, with $r\,t(a)=p$ and $r\,t(c)=q$.
Lemma 6.1.2(1) gives left homotopies $ai'\simeq_l ci''$ and
$aj'\simeq_l cj''$. Therefore their images under $G$ are equal.
The common denominator image $G(aj')$ is invertible, so cancellation
identifies the two fraction values.

**Difference from the paper:** the paper first uses Brown factorization
to replace both denominators by trivial cofibrations, then pushes out
over $B$ to obtain exactly equal extended denominators. Our proof reuses
the common-resolution construction above and allows both extended
triangles to commute up to left homotopy. This avoids that preliminary
reduction and uses the same CFA1–CFA4 hypotheses. The argument generalizes
our earlier inclusion-specific proof; no attribution to Maltsiniotis is
intended. The conclusion is stated for every weak-equivalence-inverting
functor rather than only a chosen localization.

## Lean correspondence and status

All names in the table except the class itself are in
`ABCCofibrations.IsCofibrantApproximation`.

| Statement | Declaration |
| --- | --- |
| Definition 6.1.1 | `ABCCofibrations.IsCofibrantApproximation` |
| Identity functor on an all-cofibrant category is an example | `identity` |
| Image objects are cofibrant | `obj_cofibrant` |
| Trivial cofibrations are preserved | `map_trivialCofibration` |
| Associated localizer morphism | `toLocalizerMorphism` |
| Weak equivalences are induced from the target | `toLocalizerMorphism_isInduced` |
| Object resolutions exist | `hasLeftResolutions` |
| Arrow resolutions exist | `arrow_hasLeftResolutions` |
| Common extension of resolutions | `exists_common_resolution` |
| Resolution categories are connected | `leftResolution_isConnected` |
| Lemma 6.1.2(1), with a left-homotopy witness | `leftHomotopy_of_map_postcomp_eq` |
| Cancellation under a weak-equivalence-inverting functor | `map_eq_of_map_postcomp_eq` |
| Lemma 6.1.3(1), independence of fraction choices | `fraction_map_eq_of_ambient_comparison` |

The localization equivalence for general cofibrant approximations, the bridge
to a left derivability structure, and Theorems 6.2.2(1) and 6.2.3(1) under their
full structural hypotheses remain unproved. The previously proved inclusion
case is not yet packaged as an instance of this new class. This note was
reviewed against the accompanying Lean source following commit `d1d9fa9`.

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
resolutions and arrow resolutions. Thus the resolution results alone do **not** prove the localization
equivalence. The direct inverse construction below now supplies the missing
hypothesis before we apply that constructor.

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

## Homotopy cancellation: Lemma 6.1.3(1)

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

## Independence of fractions: Lemma 6.1.4(1)

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
Lemma 6.1.3(1) gives left homotopies $ai'\simeq_l ci''$ and
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

## Fractions between prescribed resolutions and the resolution functor

Given maps $q_X:t(X)\to A$, $q_Y:t(Y)\xrightarrow{\sim}B$ and an ambient
arrow $f:A\to B$, CFA4 constructs a source fraction

$$
X\xrightarrow{i}Z\xleftarrow[\sim]{j}Y,
\qquad p:t(Z)\xrightarrow{\sim}B,
\qquad p\,t(i)=f q_X,\quad p\,t(j)=q_Y.
$$

Both $i$ and $j$ are cofibrations. To construct them, form the source sum as
$X\amalg_{\varnothing}Y$. CFA1 and CFA3 preserve this pushout and give a
map from its image to $B$, restricting to $fq_X$ and $q_Y$. Apply CFA4 to
that map. Two out of three and CFA2 show that the resulting $j$ is a weak
equivalence. No weak-equivalence assumption on $q_X$ is needed here.

Composing two such fractions uses the pushout of the first denominator and
the second numerator. Both are cofibrations, so CFA3 applies. The composite
again has two cofibration legs and an ambient weak-equivalence comparison.
Its value under any weak-equivalence-inverting functor $G$ is the composite
of the original values. If an actual source arrow lies over $f$, the
fraction value equals its image under $G$; that source arrow need not itself
be a cofibration.

Choose source objects $Q(A)$ and resolutions $q_A:t(Q(A))\xrightarrow{\sim}A$.
Taking the values of these fractions defines a functor on the ambient
category with objects $G(Q(A))$. Lemma 6.1.4(1) supplies independence of the
arrow choices and, together with pushout composition, the functor laws.
When $f$ is a weak equivalence, its fraction numerator is also a weak
equivalence, so its value is invertible. Thus this functor inverts ambient
weak equivalences.

**Difference from the paper:** this is the explicit inverse construction
in the proof of Theorem 6.1.5(1), expressed first for an arbitrary source
functor $G$ inverting weak equivalences. The chosen resolutions are parameters;
no functorial replacement is assumed. We retain the cofibration property
of both fraction legs in the Lean structure so that pushout preservation
for composition stays within CFA3. The source sum is represented by a pushout
over the initial object. The functor is constructed on the ambient category;
its lift through localization and the inverse comparison isomorphisms
are constructed in the next step below. See
[CofibrantApproximationFractions.lean](../../ABCCofibrations/CofibrantApproximationFractions.lean).

## Localization equivalence: Theorem 6.1.7(1)

Take $G$ to be localization of the source. The resolution functor $R$ inverts
ambient weak equivalences, hence lifts to $H$ from the ambient localization
to the source localization. Write $K$ for the functor induced by $t$ in the
forward direction. We construct both natural isomorphisms

$$
HK\cong 1_{\mathrm{ho}\mathcal M'},\qquad
KH\cong 1_{\mathrm{ho}\mathcal M}.
$$

Here composition is written in mathematical order; Lean's `K ⋙ H` denotes
$HK$. To construct the first comparison before localization, resolve
$t(A)$ by $q_{t(A)}:t(Q(t(A)))\to t(A)$ and compare this resolution to the
identity resolution of $t(A)$. The resulting fraction gives an invertible
arrow $G(Q(t(A)))\to G(A)$. Fraction independence and composition prove
naturality, even though $q_{t(A)}$ is an ambient map rather than necessarily
the image of a source map.

For the second comparison, a compatible isomorphism $G K\cong t L$, with
$L$ any ambient weak-equivalence-inverting functor, yields components
$G(Q(A))\mapsto L(t(Q(A)))\xrightarrow{L(q_A)}L(A)$.
Naturality follows from the numerator and denominator equations of a
resolution fraction. Mathlib's localization universal property lifts both
comparisons. They prove the general localization equivalence, independently
of the earlier inclusion-specific theorem.

**Difference from the paper:** the paper deduces Theorem 6.1.7(1) from
Theorem 6.1.5(1) and the general approximation theorem. We construct the
inverse directly from resolution fractions instead of introducing a separate
LAP1–LAP2 interface. The underlying existence and independence arguments
are the same ones used for those axioms. We then obtain mathlib's
`IsLocalizedEquivalence` and, using the already proved connected resolutions
and arrow resolutions, `IsLeftDerivabilityStructure`. The latter constructor
is applied only after the localization equivalence has been established.
The next two steps apply this bridge to the full structural statements of
6.2.2(1) and 6.2.3(1). See
[CofibrantApproximationLocalization.lean](../../ABCCofibrations/CofibrantApproximationLocalization.lean).

The references in earlier notes to cancellation as Lemma 6.1.2 and fraction
independence as Lemma 6.1.3 were numbering errors. In the pinned v4 text they
are Lemmas 6.1.3 and 6.1.4 respectively; these citations have been corrected.

## Total left derived functors: Theorem 6.2.2(1)

Let $t:\mathcal M'\to\mathcal M$ be a cofibrant approximation and
$u:\mathcal M\to\mathcal N$ a functor such that $ut$ sends trivial
cofibrations to weak equivalences. Then $u$ admits a total left derived
functor. For any such derived functor and its counit $\epsilon$, the
component $\epsilon_{t(A)}$ is invertible for every $A$ of $\mathcal M'$.
This hypothesis concerns $ut$ only; preservation on all cofibrant objects
of $\mathcal M$ is not required.

After localizing the target by $R$, the composite $Rut$ inverts trivial
cofibrations. All source objects are cofibrant, so Brown's lemma shows it
inverts every source weak equivalence. Its pointwise left derived functor
therefore exists. The left derivability structure of $t$ transfers this
existence to $Ru$. Its comparison theorem transfers invertibility of the
counit to all objects $t(A)$. The existence statement allows arbitrary
choices of source and target localizations.

**Difference from the paper:** the paper first assumes the target weak
equivalences saturated and then applies Brown's lemma. We apply Brown's
lemma directly to isomorphisms after target localization, so no saturation
or two-out-of-three hypothesis on the original target weak equivalences
is needed. Mathlib's pointwise derivability machinery supplies existence
and the counit comparison. Its left-derived convention uses a universal
counit, as explained in [derived-functors.md](derived-functors.md). The result
is proved for any derived counit, in addition to constructing one.
See [CofibrantApproximationDerived.lean](../../ABCCofibrations/CofibrantApproximationDerived.lean).

## Cofibrant restriction and derived equivalence: Theorem 6.2.3(1)

The full subcategory $\mathcal M_{cof}$ is now equipped with CF1–CF4.
We reuse mathlib's `CofibrantObject` and its inherited weak equivalences.
The cofibrations are the inverse image of the ambient cofibrations under
inclusion. The ambient initial object is initial in this full subcategory.
For a cofibration $A\to B$ and any $A\to D$ between cofibrant objects,
the ambient pushout is cofibrant because $D\to B\amalg_A D$ is a
cofibration. Fullness and faithfulness give its universal property inside
the subcategory, and the inclusion preserves it. Ambient CF4 factorizations
also remain inside the subcategory because the intermediate object is
cofibrant. These observations establish all the restricted axioms and
CFA1–CFA4 for the inclusion.

Suppose $u:\mathcal M\to\mathcal N$ is a functor between precofibration
categories whose restriction to $\mathcal M_{cof}$ is a cofibrant
approximation. That restriction preserves weak equivalences, hence sends
trivial cofibrations to weak equivalences. Theorem 6.2.1(1) gives a total
left derived functor with invertible counit on cofibrant objects.
Theorem 6.1.7(1) makes the restriction a localized equivalence. The previously
proved criterion comparing a derived functor to its localized cofibrant
restriction therefore makes the total left derived functor an equivalence.
The same criterion proves this for any total left derived functor.

**Difference from the paper:** this follows the paper's argument, using the
already proved inclusion-specific existence theorem 6.2.1(1) where the paper
invokes its generalization 6.2.2(1). The categorical equivalence criterion
was packaged separately in our earlier development. The precofibration
structure and approximation instance for the inclusion are proved from
the ambient axioms; neither is an additional assumption. The statement
allows arbitrary source and target localizations and assumes no preservation
of weak equivalences outside the cofibrant subcategory.
See [CofibrantSubcategory.lean](../../ABCCofibrations/CofibrantSubcategory.lean)
and [DerivedApproximationEquivalence.lean](../../ABCCofibrations/DerivedApproximationEquivalence.lean).

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
| Lemma 6.1.3(1), with a left-homotopy witness | `leftHomotopy_of_map_postcomp_eq` |
| Cancellation under a weak-equivalence-inverting functor | `map_eq_of_map_postcomp_eq` |
| Lemma 6.1.4(1), independence of fraction choices | `fraction_map_eq_of_ambient_comparison` |
| Fractions over prescribed resolutions | `ResolutionFraction`, `ResolutionFraction.nonempty` |
| Independence and computation on actual arrows | `ResolutionFraction.map_eq`, `ResolutionFraction.map_eq_of_hom` |
| Pushout composition and its value | `ResolutionFraction.comp`, `ResolutionFraction.map_comp` |
| Functor from chosen resolutions | `resolutionFunctor` |
| This functor inverts ambient weak equivalences | `resolutionFunctor_inverts` |
| Inverse on localizations | `localizationInverse` |
| Comparison before restricting/localizing | `resolutionFunctorRestrictionIso`, `resolutionFunctorAmbientIso` |
| Both inverse comparisons | `localizationLeftInverseIso`, `localizationRightInverseIso` |
| Equivalence with explicit resolution parameters | `localizationEquivalenceOfResolutions` |
| Theorem 6.1.7(1), no chosen resolutions in the statement | `localizedFunctor_isEquivalence` |
| Localizer equivalence | `toLocalizerMorphism_isLocalizedEquivalence` |
| General left derivability structure | `toLocalizerMorphism_isLeftDerivabilityStructure` |
| Pointwise existence under a general approximation | `hasPointwiseLeftDerivedFunctor_of_inverts_trivialCofibrations` |
| Any derived counit is invertible on image objects | `isIso_leftDerivedCounit_app` |
| Theorem 6.2.2(1) | `exists_totalLeftDerivedFunctor_of_map_trivialCofibrations` |

The general localization equivalence and its bridge to a left derivability
structure are proved. Theorem 6.2.2(1) is also proved under its full structural hypotheses.
Theorem 6.2.3(1) is also proved, and the cofibrant inclusion is now an
instance of the general approximation class.

The declarations for Theorem 6.2.3(1) are
`ABCPrecofibrationCategory.exists_totalLeftDerivedEquivalence_of_cofibrantApproximation`
and `ABCPrecofibrationCategory.isEquivalence_totalLeftDerivedFunctor_of_cofibrantApproximation`.
The subcategory instance is `ABCPrecofibrationCategory.cofibrantObject_precofibrationCategory`;
the inclusion instance is `ABCPrecofibrationCategory.cofibrantInclusion_isCofibrantApproximation`.

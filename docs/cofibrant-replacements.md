# Cofibrant replacements and the ambient localization

This note describes the first part of the comparison in Theorem 6.1.6 of
*Cofibrations in Homotopy Theory*. Only CF1–CF4 are used. Write
$\mathcal M_{\mathrm{cof}}$ for the full subcategory of cofibrant objects and
$W$ for weak equivalences.

## Differences from the paper

The intended comparison is Theorem 6.1.6 of the paper, with its CF1–CF4
hypotheses. The paper proves it through general cofibrant approximation
functors and the approximation theorem. Our construction specializes to the
inclusion $\mathcal M_{\mathrm{cof}}\hookrightarrow\mathcal M$ and constructs
a reverse functor directly, using object replacements and fractions.
Theorems here concerning that inclusion do not yet formalize the paper's
general statements for arbitrary cofibrant approximation functors.

The ambient cancellation proof follows the cylinder-boundary pushout argument
of Lemma 6.1.2(1), specialized to inclusion; we also prove the stronger variant
starting with strict homotopy after the weak equivalence. For Lemma 6.1.3(1),
we retain the paper's pushout proof for trivial-cofibration denominators and
also use a common cofibrant extension to handle general weak-equivalence
denominators directly. The replacement functor is built with explicit object
replacement parameters, rather than through the general approximation theorem.
The remaining completion status is stated below; we do not yet claim the
paper's completed equivalence.

Inclusion preserves weak equivalences, so it induces a functor

$$
\mathcal M_{\mathrm{cof}}[W^{-1}]
\longrightarrow \mathcal M[W^{-1}].
$$

This functor is **essentially surjective**: every object of the target is
isomorphic to the image of a cofibrant object. Indeed, CF4 applied to
$\varnothing\to A$ gives a cofibrant replacement $q:Q\xrightarrow{\sim}A$.
Localization turns $q$ into an isomorphism. This proves the object part of
Theorem 6.1.6. Faithfulness is now also proved, using the left inverse below;
fullness and hence the equivalence remain unproved.

## Extending a replacement across an arrow

Given $f:A\to B$ and a replacement $q:Q\xrightarrow{\sim}A$, factor $qf$
using CF4. This gives a commutative square

$$
\begin{array}{ccc}
Q & \xrightarrow{\ i\ } & R\\
{\scriptstyle q\,\sim}\downarrow &&
\downarrow{\scriptstyle r\,\sim}\\
A & \xrightarrow{\ f\ } & B,
\end{array}
$$

where $i$ is a cofibration, $r$ is a weak equivalence, and $R$ is cofibrant.
The construction keeps the prescribed source replacement. It does not
prescribe a target replacement or supply a functorial choice.

Choosing $q$ first shows that **every ambient arrow has a cofibrant
replacement square**. Both vertical maps are weak equivalences; this is
recorded using mathlib's left resolutions for the induced functor on arrow
categories.

## Comparing two replacements

For replacements $q_1:Q_1\xrightarrow{\sim}A$ and
$q_2:Q_2\xrightarrow{\sim}A$, factor their coproduct map:

$$
Q_1\amalg Q_2\xrightarrow{\ j\ }R
\xrightarrow[\sim]{\ r\ }A.
$$

The composites $i_k:Q_k\to Q_1\amalg Q_2\to R$ are cofibrations,
and $ri_k=q_k$. Two out of three makes both $i_k$ weak equivalences.
Thus the replacements admit a common extension over $A$ by trivial
cofibrations. The ambient object $A$ need not be cofibrant.

More precisely, let $\mathcal R_A$ be the category whose objects are
cofibrant replacements $q:Q\xrightarrow{\sim}A$, and whose morphisms
from $q:Q\to A$ to $q':Q'\to A$ are maps $u:Q\to Q'$ satisfying
$q'u=q$. Every such $u$ is a weak equivalence, by two out of three.
The common-extension construction gives a zigzag

$$
(Q_1,q_1)\longrightarrow(R,r)\longleftarrow(Q_2,q_2)
$$

between any two objects. Since replacements exist, $\mathcal R_A$ is
nonempty and connected. Here connected means that objects are joined by
finite zigzags of morphisms; no assertion of uniqueness of the zigzag is
needed. This is compatibility infrastructure for the remaining comparison
proof, not yet a proof of full faithfulness.

## Cancellation into an ambient object

Lemma 6.1.2(1), specialized to the inclusion of cofibrant objects, says that
for cofibrant $A,B$ and a weak equivalence $b:B\xrightarrow{\sim}B'$,

$$
bf=bg\quad\Longrightarrow\quad f\simeq_l g.
$$

The object $B'$ can be any ambient object. In fact, the formal proof allows
a strict cylinder homotopy between $bf$ and $bg$ in place of equality.
Choose a good cylinder $IA$ and glue it to $B$ along its full boundary
$A\amalg A$, using $f$ and $g$. The given homotopy defines a map from this
pushout to $B'$. Factor that map by CF4. The composite from $B$ to the
factorization object is a cofibration, and is a weak equivalence by two out
of three since its composite with the final weak equivalence is $b$.
The map out of $IA$ supplies the required homotopy after this trivial
cofibration. Equality gives a constant homotopy and hence the stated lemma.

Consequently, if $F$ is any functor on cofibrant objects that inverts weak
equivalences, then $bf=bg$ implies $F(f)=F(g)$. In particular, parallel maps
in $\mathcal R_A$ have equal images under $F$: their composites with the
target replacement map are equal by definition. This gives equality for
parallel comparison maps, beyond the connectedness result above.

The cancellation results are
`LeftHomotopyRel.of_postcomp_weakEquivalence_of_strict` and
`LeftHomotopyRel.of_postcomp_weakEquivalence_eq` in
[HomotopyCancellation.lean](../ABCCofibrations/HomotopyCancellation.lean).
The functor statement is `map_eq_of_postcomp_ambient_weakEquivalence` in
[HomotopyLocalization.lean](../ABCCofibrations/HomotopyLocalization.lean).

## Independence of fraction choices

Lemma 6.1.3(1), specialized to inclusion of cofibrant objects, is now also
formalized. Suppose $A',B',D',D''$ are cofibrant and we have two cospans

$$
A'\xrightarrow{i'}D'\xleftarrow[\sim]{j'}B',
\qquad
A'\xrightarrow{i''}D''\xleftarrow[\sim]{j''}B'.
$$

Suppose weak equivalences $\sigma':D'\to B$ and
$\sigma'':D''\to B$ to an arbitrary ambient object satisfy

$$
\sigma'i'=\sigma''i'',\qquad
\sigma'j'=\sigma''j''.
$$

Then the fractions agree in the localization of cofibrant objects:

$$
\gamma(j')^{-1}\circ\gamma(i')
=\gamma(j'')^{-1}\circ\gamma(i'').
$$

More generally they agree under any functor on cofibrant objects that
inverts weak equivalences. To prove this, take a common cofibrant extension
$h':D'\to R$, $h'':D''\to R$ of the replacements
$\sigma',\sigma''$, with $r:R\xrightarrow{\sim}B$ and
$rh'=\sigma'$, $rh''=\sigma''$. Both extended numerator maps, and both
extended denominator maps, become equal after $r$. Ambient cancellation
therefore gives equal images under the functor. Cancelling the common
invertible denominator proves equality of the fractions.

For trivial-cofibration denominators there is also a proof using the
pushout $D'\amalg_{B'}D''$, as in the paper. Both versions are in
[AmbientFractions.lean](../ABCCofibrations/AmbientFractions.lean):

| Statement | Declaration |
| --- | --- |
| Arbitrary weak-equivalence denominators | `weakEquivalence_fraction_map_eq_of_ambient_comparison` |
| Trivial-cofibration denominators | `trivialCofibration_fraction_map_eq_of_ambient_comparison` |

These results establish independence of the indicated fraction choices.

## The replacement functor

Choose a cofibrant replacement $q_A:Q_A\xrightarrow{\sim}A$ for every
ambient object. These are choices on objects; no functorial replacement in
$\mathcal M$ is assumed. Given $f:A\to B$, factor

$$
[fq_A,q_B]:Q_A\amalg Q_B\longrightarrow B
$$

as a cofibration followed by a weak equivalence $p:R\xrightarrow{\sim}B$.
Writing $i:Q_A\to R$ and $s:Q_B\to R$ for the two components gives

$$
pi=fq_A,\qquad ps=q_B.
$$

Both component maps are cofibrations, and two out of three makes $s$ a
weak equivalence. Thus $Q_A\xrightarrow{i}R\xleftarrow[\sim]{s}Q_B$
is a trivial-cofibration fraction. `ReplacementFraction` packages such a
fraction together with $p$ and its two equations; its existence and mapped
value are proved independent of the factorization choice.

For any functor $F$ on cofibrant objects that inverts trivial cofibrations,
define the extended functor by

$$
\widetilde F(A)=F(Q_A),\qquad
\widetilde F(f)=F(s)^{-1}\circ F(i).
$$

The identity law follows by comparison with the fraction represented by
$\mathrm{id}_{Q_A}$. For composition, glue the denominator of the first
fraction to the numerator of the second by a pushout. The resulting apex
still maps by a weak equivalence to the final ambient target: the pushout
map from the second apex is a trivial cofibration, and its composite with
the comparison map is the original weak equivalence. This constructs a
fraction for the composite, whose mapped value is the composite of the two
mapped fractions. Independence of choices proves the functor's composition law.

If $f$ is a weak equivalence, $pi=fq_A$ implies that $i$ is a weak
equivalence. Brown's functor lemma makes $F(i)$ invertible, so
$\widetilde F(f)$ is invertible. Taking $F$ to be localization of the
cofibrant subcategory therefore yields a functor

$$
\mathcal M[W^{-1}]\longrightarrow\mathcal M_{\mathrm{cof}}[W^{-1}].
$$

This construction and its functor laws are formalized in
[ReplacementFunctor.lean](../ABCCofibrations/ReplacementFunctor.lean).
The object replacements are explicit parameters `Q`, `q`, and `hq`.
One of the inverse comparison isomorphisms is now proved below. The other
direction **remains unproved**.

| Statement | Declaration |
| --- | --- |
| Fraction over an ambient arrow | `ReplacementFraction` |
| Existence with prescribed replacements | `ReplacementFraction.nonempty` |
| Independence of mapped value | `ReplacementFraction.map_eq` |
| Actual representative map | `ReplacementFraction.ofHom`, `ReplacementFraction.map_ofHom` |
| Pushout composition | `ReplacementFraction.comp`, `ReplacementFraction.map_comp` |
| Extension to the ambient category | `replacementFunctor` |
| Extension inverts weak equivalences | `replacementFunctor_inverts` |
| Reverse functor on localizations | `ambientLocalizationToCofibrant` |

## Restriction comparison and faithfulness

For a functor $F$ on cofibrant objects inverting weak equivalences, the maps
$F(q_A)$ for cofibrant $A$ give a natural isomorphism

$$
\widetilde F\vert_{\mathcal M_{\mathrm{cof}}}\cong F.
$$

To check naturality, the comparison $p:R\to B$ of a replacement fraction
is itself a morphism between cofibrant objects whenever $B$ is cofibrant.
The equations $pi=fq_A$ and $ps=q_B$ then imply
$F(q_B)\circ\widetilde F(f)=F(f)\circ F(q_A)$.
This gives `replacementFunctorRestrictionIso`.

Write $K$ for the inclusion-induced comparison and $H$ for the reverse
functor on localizations. Mathlib's universal property lifts the restriction
isomorphism to

$$
H\circ K\cong\mathrm{id}_{\mathcal M_{\mathrm{cof}}[W^{-1}]}.
$$

Consequently $K$ is faithful: applying $H$ to an equality of images under
$K$, then conjugating by this isomorphism, recovers equality of the original
arrows. Existence of cofibrant replacements discharges the parameters for
this faithfulness result. This does not yet prove fullness. We still need
the comparison $K\circ H\cong\mathrm{id}_{\mathcal M[W^{-1}]}$.

These are the direct-construction counterparts of part of the paper's
approximation-theorem argument, rather than a formalization of the general
approximation theorem. They are in
[ReplacementComparison.lean](../ABCCofibrations/ReplacementComparison.lean):
`cofibrantLocalizationReplacementIso` and
`cofibrantLocalizationToAmbient_faithful`.

## Lean correspondence

All declarations below are in
[CofibrantReplacement.lean](../ABCCofibrations/CofibrantReplacement.lean).

| Mathematical statement | Declaration |
| --- | --- |
| Inclusion preserves weak equivalences | `cofibrantInclusionLocalizerMorphism` |
| Every object has a replacement | `cofibrantInclusion_hasLeftResolutions` |
| Induced comparison on localizations | `cofibrantLocalizationToAmbient` |
| Comparison is essentially surjective | `cofibrantLocalizationToAmbient_essSurj` |
| Extend a prescribed source replacement | `exists_cofibrant_replacement_arrow` |
| Common extension of replacements | `exists_common_cofibrant_replacement` |
| Maps between replacements are weak equivalences | `weakEquivalence_leftResolution_hom` |
| Parallel comparison maps have equal images | `map_eq_of_leftResolution_hom` |
| Replacement categories are connected | `cofibrantInclusion_leftResolution_isConnected` |
| Every arrow has a replacement square | `cofibrantInclusion_arrow_hasLeftResolutions` |

The name “left resolution” is mathlib terminology for a weak equivalence
from an object of the source subcategory to the given ambient object.
This note was checked against the accompanying Lean source, following
commit `0746dcc`, including the accompanying `ReplacementFunctor.lean` increment.

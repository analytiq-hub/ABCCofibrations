# Cofibrant replacements and the ambient localization

This note describes the first part of the comparison in Theorem 6.1.6 of
*Cofibrations in Homotopy Theory*. Only CF1–CF4 are used. Write
$\mathcal M_{\mathrm{cof}}$ for the full subcategory of cofibrant objects and
$W$ for weak equivalences.

Inclusion preserves weak equivalences, so it induces a functor

$$
\mathcal M_{\mathrm{cof}}[W^{-1}]
\longrightarrow \mathcal M[W^{-1}].
$$

This functor is **essentially surjective**: every object of the target is
isomorphic to the image of a cofibrant object. Indeed, CF4 applied to
$\varnothing\to A$ gives a cofibrant replacement $q:Q\xrightarrow{\sim}A$.
Localization turns $q$ into an isomorphism. This proves the object part of
Theorem 6.1.6; full faithfulness, and hence the equivalence, remain unproved.

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

These results establish independence of the indicated fraction choices;
the construction of an inverse to the ambient comparison, and its functor
laws, remain to be completed.

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
commit `65065ac`.

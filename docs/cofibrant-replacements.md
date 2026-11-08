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

The name “left resolution” is mathlib terminology for a weak equivalence
from an object of the source subcategory to the given ambient object.
This note was checked against the accompanying Lean source, following
commit `9078fe4`.

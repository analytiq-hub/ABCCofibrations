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
universal property. General cofibrant approximations and Theorem 6.2.2(1)
are now formalized separately in
[the approximation development](cofibrant-approximations.md); the original
inclusion-specific proof here is retained. The dual right-derived existence
and equivalence statements are now formalized in
[the fibration development](fibration-duality.md).

The computation results below are explicit corollaries for any derived functor
with its counit and any cofibrant replacement. They are not presented as a
separately numbered theorem in the paper. The paper's proof of 5.7.1 constructs
a derived functor using chosen regular cleavages; we instead obtain the
universal object through mathlib, then derive computation and naturality from
its counit. No regular, functorial, or specially normalized choice of
replacements is required for these corollaries.

The comparison and equivalence criterion below isolate the categorical step
in the proof of Theorem 6.2.3(1). Instead of assuming that the original
functor's restriction is a cofibrant approximation, we assume directly that
its localization lift is an equivalence, and prove this condition is also
necessary. The structural hypothesis now implies this condition in
[DerivedApproximationEquivalence.lean](../../ABCCofibrations/DerivedApproximationEquivalence.lean),
completing Theorem 6.2.3(1); see the
[approximation note](cofibrant-approximations.md) for the proof and its
comparison with the paper.
The localizer formulation below works with a target weak-equivalence class
satisfying two out of three. This follows automatically if the target is a
precofibration category, as in 6.2.3(1); no target cofibrations or model
structure are needed for this formulation. Unlike 6.2.1(1), where target
localization alone suffices, this two-out-of-three hypothesis is used to
construct a localizer morphism before localizing the target.

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

## Computing with a replacement

For this section, let $F:\mathcal M\to\mathcal H$ invert trivial
cofibrations between cofibrant objects, let $L$ localize $\mathcal M$, and
let $LF$ be any left derived functor with counit $\varepsilon$.
For a cofibrant replacement $q:Q\xrightarrow{\sim}A$, define

$$
c_q:LF(L(A))\xrightarrow{\cong}F(Q),\qquad
c_q=\varepsilon_Q\circ LF(L(q))^{-1}.
$$

This is an isomorphism because localization inverts $q$ and
$\varepsilon_Q$ is invertible for cofibrant $Q$. It satisfies

$$
c_q\circ LF(L(q))=\varepsilon_Q,
\qquad F(q)\circ c_q=\varepsilon_A.
$$

The second equation computes the ambient counit even when $A$ is not
cofibrant; it does not assert that $F(q)$ is invertible.

Given replacements $q:Q\to A$, $r:R\to B$ and maps $f:A\to B$,
$a:Q\to R$ satisfying $ra=fq$, the following square commutes:

$$
\begin{array}{ccc}
LF(L(A)) & \xrightarrow{LF(L(f))} & LF(L(B))\\
{\scriptstyle c_q}\downarrow && \downarrow{\scriptstyle c_r}\\
F(Q) & \xrightarrow{F(a)} & F(R).
\end{array}
$$

Indeed, precompose the desired equation with the invertible $LF(L(q))$.
The replacement square moves this map through to $LF(L(r))$, and the
remaining equation is naturality of $\varepsilon$ at $a$. The map $a$
need not be a cofibration.

For two replacements $q:Q\to A$ and $r:R\to A$, the comparison

$$
d_{q,r}=c_r\circ c_q^{-1}:F(Q)\xrightarrow{\cong}F(R)
$$

exists without choosing a map between them. If $a:Q\to R$ satisfies
$ra=q$, then $d_{q,r}=F(a)$. These comparisons satisfy
$d_{q,q}=\mathrm{id}$ and $d_{r,s}\circ d_{q,r}=d_{q,s}$.
Here “canonical” is relative to the given derived functor and its counit.
For a total left derived functor of $u$, apply these results to
$F=\gamma_{\mathcal N}\circ u$.

## Comparing with the localized restriction

Let $F$, $L$, and $(LF,\varepsilon)$ be as in the computation section.
Brown's lemma allows the restriction of $F$ to cofibrant objects to factor
through localization. Write this lift as

$$
\overline F:\mathcal M_{\mathrm{cof}}[W^{-1}]\longrightarrow\mathcal H.
$$

For the comparison
$K:\mathcal M_{\mathrm{cof}}[W^{-1}]\to\mathcal D$ induced by $L$,
there is a natural isomorphism

$$
LF\circ K\cong\overline F.
$$

The localized restriction is a left derived functor of the restricted $F$,
with invertible counit. Mathlib's comparison theorem for the left
derivability structure of cofibrant inclusion therefore supplies this
isomorphism. It depends on the given counit, so it applies to any derived
functor satisfying the universal property.

Since $K$ is an equivalence, the comparison gives

$$
LF\text{ is an equivalence}\quad\Longleftrightarrow\quad
\overline F\text{ is an equivalence}.
$$

In particular, if $\overline F$ is an equivalence, the earlier existence
theorem produces a derived equivalence with counit invertible on cofibrant
objects. For a total left derived functor of $u$, take
$F=\gamma_{\mathcal N}\circ u$.

With the canonical ambient localization and explicit object replacements,
let $H$ denote `ambientLocalizationToCofibrant`, the reverse functor
constructed earlier. The inverse comparison $KH\cong\mathrm{id}$ and
the restriction comparison give

$$
LF\cong\overline F\circ H.
$$

This identifies the abstract derived functor with the construction via
cofibrant replacements as a functor, extending the object and square
computation formulas above. These comparison results are in
[DerivedFunctorComparison.lean](../../ABCCofibrations/DerivedFunctorComparison.lean).

## The localizer formulation of the equivalence criterion

Let $u:\mathcal M\to\mathcal N$ send trivial cofibrations with cofibrant
source to weak equivalences, and assume $W_{\mathcal N}$ satisfies two out
of three. Brown's lemma proves that $u$ preserves all weak equivalences
between cofibrant objects. It therefore defines a morphism of localizers

$$
u_{\mathrm{cof}}:(\mathcal M_{\mathrm{cof}},W_{\mathrm{cof}})
\longrightarrow(\mathcal N,W_{\mathcal N}).
$$

In mathlib, `IsLocalizedEquivalence` means that the induced functor on the
canonical localizations is an equivalence; mathlib transfers this property
to any choices of localization functors. Applying the preceding comparison
with $F=\gamma_{\mathcal N}\circ u$ gives

$$
\mathbf L u\text{ is an equivalence}\quad\Longleftrightarrow\quad
u_{\mathrm{cof}}\text{ is a localized equivalence}.
$$

The statement applies to any total left derived functor with its counit,
and to any source and target localization functors. If the localizer condition
holds, the existence theorem produces a total left derived equivalence with
counit invertible on cofibrant objects. The original functor need not preserve
weak equivalences with noncofibrant endpoints.

These results are in
[DerivedEquivalence.lean](../../ABCCofibrations/DerivedEquivalence.lean).
The general approximation axioms now imply this localizer condition by the
proved localization equivalence, completing 6.2.3(1). The cofibrant
subcategory structure is established in
[CofibrantSubcategory.lean](../../ABCCofibrations/CofibrantSubcategory.lean).

## Lean correspondence and status

| Mathematical result | Declaration |
| --- | --- |
| Cofibrant inclusion is a left derivability structure | `cofibrantInclusion_isLeftDerivabilityStructure` |
| Pointwise existence for an inverting functor | `hasPointwiseLeftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations` |
| Any derived counit is invertible at cofibrant objects | `isIso_leftDerivedCounit_app_cofibrant` |
| Existence with universal property and counit statement | `exists_leftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations` |
| Theorem 6.2.1(1), with target localization | `exists_totalLeftDerivedFunctor_of_map_trivialCofibrations` |
| Compute the derived value from a replacement | `leftDerivedObjIsoOfCofibrantReplacement` |
| Recover the counit at the replacement source | `map_comp_leftDerivedObjIsoOfCofibrantReplacement_hom` |
| Compute the ambient counit | `leftDerivedObjIsoOfCofibrantReplacement_hom_comp_map` |
| Naturality for a replacement square | `leftDerivedObjIsoOfCofibrantReplacement_naturality` |
| Compare two computed values | `leftDerivedReplacementComparisonIso` |
| Comparison equals the functor image of a map over the ambient object | `leftDerivedReplacementComparisonIso_hom_eq_map` |
| Coherent identity and composition | `leftDerivedReplacementComparisonIso_refl`, `leftDerivedReplacementComparisonIso_trans` |
| Localized cofibrant restriction | `cofibrantRestrictionLift` |
| Comparison after cofibrant inclusion | `leftDerivedFunctorCofibrantRestrictionIso` |
| Necessary and sufficient equivalence criterion | `isEquivalence_leftDerivedFunctor_iff_cofibrantRestrictionLift` |
| Existence of a derived equivalence under that criterion | `exists_leftDerivedEquivalence_of_cofibrantRestrictionLift` |
| Comparison with the replacement construction | `leftDerivedFunctorIsoViaReplacements` |
| Restriction as a morphism of localizers | `cofibrantRestrictionLocalizerMorphism` |
| Inversion after target localization | `inverts_cofibrant_trivialCofibrations_after_localization` |
| Total derived equivalence iff localized equivalence of the restriction | `isEquivalence_totalLeftDerivedFunctor_iff_localized_cofibrantRestriction` |
| Existence of a total derived equivalence under that condition | `exists_totalLeftDerivedEquivalence_of_localized_cofibrantRestriction` |

All these results are proved. General cofibrant approximations and the full
structural formulation of 6.2.3(1) are now proved in the companion modules
linked above. The dual statements 6.2.1(2)–6.2.3(2) are also proved;
Quillen adjunctions are now proved using Maltsiniotis's argument; see
[the adjunction note](quillen-adjunctions.md).
This note was reviewed against the accompanying Lean source following commit
`5bd8271`, including the localizer formulation of derived equivalences.

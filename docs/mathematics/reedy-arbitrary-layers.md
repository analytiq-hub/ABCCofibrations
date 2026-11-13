# Arbitrary degree layers and small direct colimits

This note covers Lemma 9.3.2(1), Theorem 9.3.5(1)–(2)(a–c), and
Theorems 9.4.1–9.4.3(1)–(2)(a–c) of Rădulescu-Banu's
[*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4).
The ambient category is an ABC precofibration category, with the indicated
parts of CF5 and CF6 supplied separately. The native inverse statements use
an ABC prefibration category and the dual axioms.

Unlike the earlier finite results, these statements place no finiteness
condition on the objects or hom-sets of the indexing categories.

## Attaching a layer

Let $P$ be a full subcategory of a small category $D$. Suppose that every
arrow whose source lies outside $P$ is an identity, allowing transport
along equality of objects. Write $S$ for the set of objects outside $P$.
For a diagram $X$, every proper predecessor of an object $d\in S$ belongs
to $P$. Hence the latching cocone gives a map
$L_dX\to\operatorname{colim}_P X$.

The whole colimit is the pushout

$$
\begin{array}{ccc}
\displaystyle\coprod_{d\in S} L_dX
&\longrightarrow&\displaystyle\coprod_{d\in S} X_d\\
\downarrow&&\downarrow\\
\operatorname{colim}_P X&\longrightarrow&\operatorname{colim}_D X.
\end{array}
$$

`ReedyLayer.lean` constructs a cocone on $X$ from this pushout and proves
its universal property. This is the categorical content of Lemma 9.3.2(1).
If $X$ is Reedy cofibrant and the old colimit is cofibrant, CF5(1) supplies
the two coproducts and makes the top arrow a cofibration. CF3 then supplies
the pushout and makes the bottom arrow a cofibration. Its target is
cofibrant as well. The public theorem is `colimit_isPushout_layer`.

For maps of diagrams, `CoproductPushouts.lean` proves that a coproduct of
pushout squares is a pushout, assuming only the coproducts concerned.
`ReedyLayerMaps.lean` proves naturality of the attaching square and uses
this categorical lemma to identify the coproduct of relative latching
pushouts. Gluing then gives both the map on whole colimits and its
relative comparison as cofibrations (`ReedyLayer.cofibration_step`).

## Bounded and unbounded diagrams

Choose a direct degree function $\deg:D\to\mathbb N$. For diagrams with
$\deg(d)<N$, induction on $N$ attaches all objects of degree $N-1$ at once.
The layer may have infinitely many objects. Applying the same induction
to latching diagrams proves the map statements.

`ReedyBounded.lean` proves colimit existence, cofibrancy, and cofibration
transition maps between successive degree truncations.
`ReedyBoundedMaps.lean` proves preservation of Reedy cofibrations and of
pointwise weak equivalences for bounded diagrams. Only the latter uses
the trivial-cofibration clause CF5(2).

For unbounded degrees, form the sequence

$$
C_nX=\operatorname{colim}_{\deg(d)<n} X_d.
$$

Each $C_nX$ is cofibrant, and $C_nX\to C_{n+1}X$ is a cofibration. CF6(1)
constructs its colimit. The categorical reconstruction and naturality
already proved in `DegreeColimits.lean` identify it with
$\operatorname{colim}_D X$.

For a Reedy cofibration $f:X\to Y$, each $C_nf$ is a cofibration, and

$$
C_nY\amalg_{C_nX} C_{n+1}X\longrightarrow C_{n+1}Y
$$

is a cofibration. `reedyCofibration_degree_step` constructs these relative
pushouts using the whole-layer gluing theorem. The sequential Reedy
cofibration theorem then applies. For pointwise weak equivalences, the
bounded map theorem and the sequential weak-equivalence theorem apply.

The public absolute results are:

| Paper statement | Lean theorem | Additional axioms |
| --- | --- | --- |
| 9.3.5(1)(a) | `reedyCofibrant_colimit_small` | CF5(1), CF6(1) |
| 9.3.5(1)(b) | `reedyCofibration_colimMap_small` | CF5(1), CF6(1) |
| 9.3.5(1)(c) | `reedyCofibrant_colimMap_weakEquivalence_small` | CF5(1–2), CF6(1–2) |
| 9.3.5(2)(a) | `reedyFibrant_limit_small` | F5(1), F6(1) |
| 9.3.5(2)(b) | `reedyFibration_limMap_small` | F5(1), F6(1) |
| 9.3.5(2)(c) | `reedyFibrant_limMap_weakEquivalence_small` | F5(1–2), F6(1–2) |

The inverse results are obtained by applying the direct results in the
opposite category and comparing with mathlib's native chosen limits and
`limMap`. There is no independent inverse induction. Native F5/F6 are
represented by the corresponding split CF5/CF6 assumptions on the
opposite ambient category.

`SequentialColimits.lean` also exposes
`cofibration_comparison_colimit_of_reedy`: the relative comparison from
$G_0\amalg_{F_0}\operatorname{colim}F$ to $\operatorname{colim}G$ is a
cofibration for a Reedy cofibration of sequences. Its statement allows
any representative pushout. This will support the general relative theorem.

## Pointwise Kan extensions

For $u:D_1\to D_2$, with $D_1$ small direct and $D_2$ any small category,
the comma category $(u\downarrow d_2)$ is direct. Its latching restriction
and final comparison were already proved in `ReedyKan.lean`; they never
required finiteness. Applying the new absolute results removes the finite
source and finite hom-set restrictions from the pointwise Kan theorem.

`ReedySmallKan.lean` proves 9.4.2(1)(a–c), including preservation statements
for `pointwiseLeftKanMap`, the actual morphism between individually existing
chosen Kan extensions. It assumes `ABCCofibrationCategory` in the indexing
universe. `ReedySmallRightKan.lean` proves 9.4.2(2)(a–c) for the native chosen
right extensions and their maps, entirely by duality and the existing
`KanOpposite.lean` comparisons. The target indexing category need not be
direct or inverse for these pointwise results.

## Relative colimits and Reedy Kan extensions

`ReedyRelativeBounded.lean` proves
`reedyCofibrant_colimit_pre_bounded_outside`. Only the objects outside a
fully faithful open source need bounded degrees; the source itself may
be unbounded. Induction attaches the highest remaining complementary
layer, retaining the entire old source. It uses only CF5(1) beyond CF1–CF4.

`ReedySmallRelativeColimits.lean` proves 9.4.1(1)(a) and (c) without any
finiteness restriction. For (a), define a new, monotone degree

$$
\delta(d)=\begin{cases}0&d\in P,\\\deg(d)+1&d\notin P.\end{cases}
$$

Its stage zero is empty; stage one is exactly $P$; later stages adjoin
bounded-degree objects outside $P$. The new degree need not be strict on
$P$. This causes no problem: the categorical reconstruction in
`DegreeColimits.lean` requires only monotonicity, while each truncation
remains a direct category with its original degree. The relative bounded
theorem makes the transition maps cofibrations. `SequenceTails.lean`
proves that CF6 gives a cofibration from every stage into the sequential
colimit, so the stage-one map proves the result for $P$.

The theorem `reedyCofibrant_colimit_pre_small` also permits an arbitrary
fully faithful open presentation of the subcategory, transferring through
its object image. Part (c) follows from the absolute weak-equivalence
theorem, the restriction cofibration from (a), and excision. The actual
relative comparison is a weak equivalence; no Reedy cofibration hypothesis
on the map is added.

`ReedySmallRelativeLimits.lean` transports these results to 9.4.1(2)(a–c)
for native limits and pullbacks. It uses the existing opposite comparison
maps and assumes a full ABC fibration category. The direct statements keep
the split assumptions: (a) and (b) use CF5(1), CF6(1), and (c) uses both clauses.

For (b), `ReedyRelativeDegreeMaps.lean` permits a degree that is constant
on the old zero layer and strict on arrows out of positive-degree objects.
It proves cofibration comparisons for all successive truncations, handling
the empty stage separately. `SequenceTails.lean` extends the relative
sequential comparison to any stage, including stage one, which represents
$P$. `ReedySmallRelativeMaps.lean` identifies its comparison with the chosen
whole pushout using the naturality of the reconstruction isomorphisms.
It also allows an arbitrary fully faithful open presentation of $P$, so
the native inverse proof can reuse it through opposites.

These results also establish 9.4.3(1)–(2)(a–c) in
`ReedySmallKanReedy.lean` and `ReedySmallRightKanReedy.lean`. The boundary
comma colimit is cofibrant and its inclusion is a cofibration by the new
relative theorem. The existing universal cocone in
`KanLatchingComparison.lean` identifies it with the Kan extension's
latching object. Both source and target are small direct categories,
or small inverse categories on the dual side. No finiteness condition
remains. The inverse proof reuses the direct proof and transports Reedy
cofibrancy and Reedy cofibrations across the canonical isomorphisms of Kan
extensions. Part (b) applies the full relative comparison at the boundary.

## Differences from the paper and remaining work

The layer lemma is stated with an explicit condition that arrows out of
new objects are identities. Its categorical proof consequently needs
neither a chosen degree nor a directness instance. Equal-degree layers
with open complement, as in the paper, satisfy this condition. This is a
general categorical formulation of the same attachment argument.

The proof constructs the universal cocone explicitly, splits CF5 and CF6
into their cofibration and trivial-cofibration clauses, and tracks the
coproduct indexing universe. Latching colimits are supplied explicitly,
as in our existing representation of Reedy cofibrancy. No unrestricted
ambient colimits, extra homotopical axioms, or functorial factorizations
are assumed. The inverse proofs are transported rather than repeated.
The collapsed degree packages the paper's relative filtration for reuse
of the existing absolute categorical reconstruction. The Kan latching
comparison uses the already documented cocone proof in place of the
paper's Grothendieck construction.

The absolute theorem 9.3.5, relative theorem 9.4.1, pointwise Kan theorem
9.4.2, and Reedy Kan theorem 9.4.3 are now available in all parts on both
sides, without finiteness restrictions. Their older finite specializations
remain useful under weaker ambient axioms.

The CF1–CF4 part of 9.2.4(1)(a),(b) is now implemented for arbitrary small
direct categories. The whole-layer factorization, a compatible tower, and
categorical gluing prove the unrestricted CF4 theorem using CF5(1) without
CF6. Native inverse factorization follows by duality. See
[the layer factorization note](reedy-layer-factorization.md) for the exact
statements and differences from the paper. Full Reedy CF5–CF6, unrestricted
pointwise CF5–CF6, and transport of the new instances to native inverse
structures remain outstanding.

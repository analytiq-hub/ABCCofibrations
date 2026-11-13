# Reedy pushouts and the layer factorization construction

This note concerns Corollary 9.3.6 and the proof of Theorem 9.2.4(1)(a) in
Rădulescu-Banu's [*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4).
The unrestricted colimit and relative-colimit theorems used here are described
in [the arbitrary-layer note](reedy-arbitrary-layers.md).

The factorization axiom is now proved for every small direct category,
and its native inverse version follows by duality. The construction below
first assembles each layer, then glues one compatible tower of factorizations.
The full Reedy CF5–CF6 structure is still outstanding.

## Pointwise cofibrations and pushouts

`ReedySmallStructure.lean` proves Corollary 9.3.6 for every small direct or
inverse category. A Reedy cofibration induces cofibrations on both latching
objects and diagram values. For a Reedy fibration the corresponding maps of
matching objects and values are fibrations. The inverse result is a direct
application of the cofibration result in the opposite categories.

On the direct side the proof restricts to the latching category and applies
9.3.5(1)(b). The component map then factors through the relative latching
pushout, exactly as in the paper. CF5(1) and CF6(1) suffice; the trivial-map
clauses are not used.

The module also proves existence of the pointwise pushouts required by CF3,
preservation of Reedy cofibrations under pushout, and preservation of pointwise
weak equivalences when the pushed-out map is a trivial Reedy cofibration.
These statements assume a full ABC cofibration category and place no finiteness
restriction on the direct indexing category. The proof reuses the existing
categorical theorem that colimits commute with the particular pushouts in
question, followed by gluing. It does not assume unrestricted cocompleteness.
These are standalone CF3 results, rather than a declaration of the full
infinite-diagram cofibration-category instance.

## Extending over a maximal layer

Let $P$ be a full subcategory of a small category $D$, and suppose that every
arrow out of an object outside $P$ is an identity, allowing equality transport.
Then $P$ is closed under predecessors. Let $F:P\to M$ be an old diagram.
For each new object $d$, supply a cocone $c_d$ on the diagram of its predecessors
in $P$.

`ReedyLayerExtension.lean` constructs a whole diagram whose old values are those
of $F$ and whose new value at $d$ is the vertex of $c_d$. Its arrows are:

- the old arrows of $F$ between old objects;
- the cocone legs for arrows from old objects to new objects;
- identity transports for arrows whose source is new.

`extensionRestrictIso` compares its old restriction with $F$.
`extensionLatchingIso` identifies the latching diagram at each new object with
$F$ on its predecessors, and `extensionLatchingIso_hom_desc` identifies the
latching map with the chosen cocone map under the source and target comparisons.
`extensionHom` constructs compatible maps between two such extensions.
`extensionIso` recovers an existing whole diagram when its own canonical
cocones are used. The extension functor and compatible maps require no cofibration axioms,
colimits, or finiteness assumptions. The latching-map comparison assumes
only the individual colimits occurring in its statement.

## The new latching objects

Suppose now that $D$ is direct and that $F$ is Reedy cofibrant.
`ReedyLayerLatching.lean` proves that its restriction to the predecessors of a
new object $d$ is Reedy cofibrant. The comparison of local latching categories
is fully faithful and essentially surjective; its finality transfers latching
colimits and their cofibrations. The same construction preserves Reedy
cofibrations of old diagrams.

All predecessors have degree strictly less than $\deg(d)$. Consequently the
bounded colimit theorem constructs the new latching object and proves it
cofibrant using CF5(1), without CF6. The induced map of new latching objects
is likewise a cofibration for a Reedy cofibration of old diagrams.

## The compatible local CF4 step

Let $f:X\to Y$, with $X$ Reedy cofibrant. Suppose a factorization has already
been chosen on $P$:

$$
X|_P\xrightarrow{a} Z\xrightarrow{r}Y|_P,
\qquad ar=f|_P,
$$

where $Z$ is Reedy cofibrant. For each new object $d$, form

$$
Q_d=X_d\amalg_{L_dX} L_dZ.
$$

Here $L_dZ$ denotes the colimit of the old diagram $Z$ on the predecessors of
$d$; it exists by the preceding construction. The compatibility $ar=f|_P$
defines a map $Q_d\to Y_d$. Its source is cofibrant by CF3. Apply CF4:

$$
Q_d\xrightarrow{k_d} Z_d\xrightarrow{p_d}Y_d,
\qquad k_d\text{ a cofibration},\quad p_d\text{ a weak equivalence}.
$$

`ReedyLayer.exists_factorization_at_new_object` in
`ReedyLayerFactorization.lean` returns this data together with the cocone
$c_d$ on $Z$, the map $i_d:X_d\to Z_d$, and all equations needed for assembly.
For every predecessor arrow $j:e\to d$ they are

$$
X(j)i_d=a_e(c_d)_j,\qquad
(c_d)_j p_d=r_eY(j),\qquad
i_dp_d=f_d.
$$

It also returns the pushout square defining $Q_d$ and the equations identifying
its comparison $k_d$ with $i_d$ and the colimit map of $c_d$. Thus the relative
cofibration required at the new object is explicit, rather than inferred from
pointwise cofibrancy. The local construction uses CF1–CF4 and CF5(1), with no
CF6 or functorial factorization assumption.

## Assembling the layers and the whole factorization

`ReedyOpenReflection.lean` transfers latching colimits and relative comparisons
back from an open restriction. `ReedyLayerReedy.lean` uses it at old objects and
the explicit latching isomorphism at new objects to prove that the assembled
extension is Reedy cofibrant and its incoming map is a Reedy cofibration.
`extensionLift` and `extensionDesc` supply the two natural transformations.

`ReedyLayer.factorization_layer` now extends a chosen old factorization over
the whole maximal layer. It returns a restriction isomorphism to the old
middle diagram and equations comparing both factorization maps.
`ReedyBoundedFactorization.lean` applies this construction by induction on a
degree bound, without restricting the number of objects or arrows.
`ReedyBoundedFibFactorization.lean` gives the native inverse result by duality.

`ReedyOpenFunctor.lean` proves that fully faithful, injective-on-objects open
functors preserve Reedy data. This handles the different presentations of the
old truncation inside the next truncation. `ReedyTruncationFactorization.lean`
extends any chosen truncation factorization to a compatible successor.
`ReedyFactorizationTower.lean` uses dependent choice to construct one tower,
including the adjacent restriction isomorphisms and their map equations.

`DegreeDiagramGluing.lean` is categorical. It composes the adjacent isomorphisms
to comparisons between all stages and proves their cocycle identity. At an
object $d$, the whole diagram uses its value at stage $\deg(d)+1$. An arrow
is evaluated in the first stage containing its target, with its source
transported by the comparison isomorphism. Naturality and the cocycle identity
prove the functor laws. Compatible left and right maps are glued as well.
The resulting restriction to every truncation is canonically isomorphic to
the chosen stage. No ambient colimit is used for this gluing.

`reedy_factorization_small` in `ReedySmallFactorization.lean` applies this
construction to the chosen tower. Every object's latching category lies in a
truncation containing that object, so the Reedy conditions transfer back
from that truncation. Pointwise weak equivalence and the factorization equation
are checked at the first stage containing the object. This proves the full
CF4 statement using CF1–CF4 and CF5(1), without CF6. The native F4 theorem
`reedy_fibration_factorization_small` in `ReedySmallFibFactorization.lean`
applies this theorem to the opposite diagram; no second construction is used.

`SmallDiagramPrecategory.lean` now gives CF1–CF4 instances for both
`ReedyDiagram D M` and `PointwiseDiagram D M` when $D$ is small direct and
$M$ is an ABC cofibration category in the indexing universe. The pointwise
factorization uses a Reedy replacement and the existing pushout argument,
as in the earlier finite proof. The new instances have lower priority than
the finite instances, retaining those results under weaker ambient assumptions.

## Differences from the paper and remaining work

The mathematical construction follows the paper's degree induction. The Lean
implementation separates the categorical extension, local latching comparison,
and CF4 choice, and allows an arbitrary maximal complementary layer instead of
requiring a degree layer in every statement. Indexing universes and the
particular latching colimits are explicit.

The local CF4 theorem only requires the middle old diagram $Z$ to be Reedy
cofibrant; it does not require the old map $a$ itself to be a Reedy cofibration.
The stronger old-map hypothesis is used when proving the assembled map Reedy.
This generalizes the local step without weakening the final factorization axiom.

The paper's instruction to continue degree by degree is implemented by a
chosen tower with explicit comparison isomorphisms, followed by categorical
gluing. The standalone factorization theorem isolates CF5(1) and shows that
CF6 is unnecessary. The diagram-category instances currently assume the full
ambient ABC cofibration category, as in the paper. No functorial factorization,
unrestricted ambient cocompleteness, or additional axioms are assumed.

Still required: transport the new diagram-category instances to native inverse
diagram structures; prove Reedy CF5 and CF6; and extend the existing finite
pointwise CF5–CF6 instances to arbitrary small diagrams, keeping the coproduct
indexing universe separate from the indexing category's universe where needed.
The native inverse factorization theorem itself is already implemented.

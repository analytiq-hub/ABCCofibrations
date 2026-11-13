# Reedy pushouts and the layer factorization construction

This note concerns Corollary 9.3.6 and the proof of Theorem 9.2.4(1)(a) in
Rădulescu-Banu's [*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4).
The unrestricted colimit and relative-colimit theorems used here are described
in [the arbitrary-layer note](reedy-arbitrary-layers.md).

The infinite-diagram factorization axiom is **not yet proved**. The current
implementation proves the pointwise consequences, pushout axiom, categorical
layer extension, and the compatible local factorization at each new object.

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

## Differences from the paper and remaining work

The mathematical construction follows the paper's degree induction. The Lean
implementation separates the categorical extension, local latching comparison,
and CF4 choice, and allows an arbitrary maximal complementary layer instead of
requiring a degree layer in every statement. Indexing universes and the
particular latching colimits are explicit.

The local CF4 theorem only requires the middle old diagram $Z$ to be Reedy
cofibrant; it does not require the old map $a$ itself to be a Reedy cofibration.
The stronger old-map hypothesis will be needed when proving the assembled map
Reedy. This is a generalization of the local step, not a weakening of the
factorization axiom to be proved.

Still required for the infinite CF4 theorem: combine the local choices using
`extensionHom` and `extensionIso`; prove Reedy cofibrancy and the Reedy
cofibration property for the resulting whole layer; choose these extensions
compatibly through the degree truncations; and assemble the whole diagram and
its two factorization maps. The existing finite factorization theorem remains
unchanged. Full Reedy CF5 and CF6, followed by the infinite diagram-category
instances and their duals, also remain outstanding.

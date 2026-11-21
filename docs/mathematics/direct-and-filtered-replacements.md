# Reducing indexing categories to direct categories, posets, or filtered categories

This note collects constructions relevant to reducing homotopy colimits indexed
by an arbitrary small category. It distinguishes established reference results,
candidate repairs of our source, and the exact current Lean implementation.
The main source remains Rădulescu-Banu, *Cofibrations in Homotopy Theory*,
math/0610009v4, especially §§9.5–9.6.

## Terminology and the obstruction to an arbitrary filtered replacement

A **direct category** in this project admits a degree function to the natural
numbers that strictly increases along every nonidentity arrow. Parallel arrows
are allowed. This is `ABCCofibrations.IsDirect`.

A **filtered category** is nonempty, admits a common receiving object for each
pair of objects, and admits an equalizing postcomposition for each parallel
pair of arrows. A **directed poset** is a nonempty poset in which every finite
set has an upper bound. Its associated category is filtered. A poset need not
be directed, and a direct category need not be filtered. An arbitrary directed
poset can also have chains too long for a natural-number degree, so it need
not satisfy our `IsDirect` definition.

There cannot be a homotopy-final functor from a filtered category to every
small category. A filtered category has weakly contractible nerve. A
homotopy-final functor induces an equivalence of classifying-space homotopy
types. Taking the target to be the one-object category of a nontrivial group
would therefore assert that its classifying space is weakly contractible.
This is an obstruction to a uniform homotopy-cofinal filtered replacement;
it does not rule out a special reformulation for a particular diagram.

For a functor q : J → I, a usable homotopy-colimit comparison has the form

$$\operatorname{hocolim}_{J} q^*X\;\simeq\;\operatorname{hocolim}_{I} X.$$

A weak equivalence of classifying spaces BJ → BI alone does not establish this
for arbitrary diagrams X. Nor does ordinary categorical cofinality alone imply
homotopy cofinality. Specify the relevant comma-category direction rather than
relying on the inconsistent terms “left” and “right cofinal.” For homotopy
colimits the standard homotopy-final criterion uses (i ↓ q).

## Comparison of constructions

| Construction | Input | Resulting index or model | What must justify the homotopy-colimit comparison | Current repository status |
|---|---|---|---|---|
| Semisimplicial direct resolution Δ′I / DI | Any small category I | A direct category of all finite labelled chains, with injective ordinal maps | Restricted Reedy diagrams, replacement, and the terminal-projection approximation | Resolution, degree, projection, and naturality checked; full approximation remains |
| Vertex insertion | A resolution or relevant comma/fiber category | An endofunctor and natural-transformation zigzag contracting it | Naturality, then the required homotopy/cofinality and Reedy comparisons | Zigzag for Δ′ checked; labelled terminal-chain insertion checked; general contraction remains |
| Marked terminal vertices | An object i of I | A direct category of chains whose terminal vertex is marked i; maps preserve the mark | Comparison with the original comma category and preservation of Reedy cofibrancy | Initial singleton, directness, constant Reedy diagrams checked; naive finality fails |
| Categorical subdivision Sd(I), Sd²(I) | Any small category I | A subdivision category, then a poset | A diagram-sensitive cofinality/localization theorem, not merely BI-equivalence | Literature candidate; no implementation |
| Simplicial replacement / two-sided bar | A diagram X on I, with suitable homotopical structure | A simplicial diagram formed from coproducts over chains in I | Realization/bar comparison and cofibrancy hypotheses | Literature candidate; existing coproduct/sequential APIs are prerequisites |
| Bounded diagrams on the nerve | Any small I and a suitable model approximation | Diagrams on the simplex category with degeneracies sent to isomorphisms | Bousfield–Kan model approximation and its derived-colimit comparison | Literature candidate; different ambient assumptions from ABC axioms |
| Cofinal directed-poset replacement | A small **filtered** category I | A directed poset mapping cofinally to I | Filtered comma categories give the homotopy-final refinement | Ordinary-colimit theorem located; not implemented here |

## 1. The semisimplicial direct resolution

An object of Δ′I is a functor [n] → I. A map to [m] → I is an injective monotone
map [n] → [m] commuting with the labels. Include degenerate labelled chains:
identity arrows in I do not make a simplex disappear. The degree is n, and the
terminal projection sends a chain to its final label.

This is the direct replacement used in Rădulescu-Banu §9.5, Cisinski §6.12,
and Szumiło's DI construction. The relevant reduction involves diagrams that
send maps projecting to identities to weak equivalences. The paper then uses
Reedy replacements and the relative colimit along the projection. It is not
an assertion that the projection is an equivalence of ordinary categories.

The implementation is `SemisimplicialResolution.lean`; the native inverse
construction is obtained from the resolution of Iᵒᵖ by taking opposites.
See [the resolution note](semisimplicial-resolution.md) for exact declarations.

## 2. Vertex insertion: repair without an initial object

For Δ′ itself, insert an extra vertex into every ordinal, and extend each
embedding by carrying new vertices to new vertices. There are natural maps
from the old ordinal and from the one-vertex ordinal to the enlarged ordinal:

$$\mathrm{id}\;\longrightarrow\;s\;\longleftarrow\;\mathrm{const}[0].$$

This gives the categorical contraction data even though Δ′ has no initial
object. Szumiło gives a labelled version for D[n] → [n], with a section and
natural weak equivalences; see Lemma 3.9 of
[*Two Models for the Homotopy Theory of Cocomplete Homotopy Theories*,
arXiv:1411.0303v1](https://arxiv.org/pdf/1411.0303v1).
The published *Frames in cofibration categories* uses different numbering.

`SemisimplexContraction.lean` checks this zigzag for Δ′ by inserting a first
vertex. `ResolutionVertexInsertion.lean` checks insertion of a terminal
label using mathlib's `WithTerminal` construction. A labelled construction
needs a compatible arrow to the new label, supplied by a terminal object or
the structural arrow in a comma category. One cannot simply insert an arbitrary
label into an arbitrary chain.

The correction is substantive: Lemma 9.5.2(1)(a)'s assertion of an initial
object is false for the full fiber. Even for the terminal category there are
two singleton-to-edge face maps. `SemisimplexCounterexample.lean` checks this
obstruction. Contractibility can survive, but the proof of Proposition 9.5.4
also uses the initial object to build a natural weak equivalence from a Reedy
cofibrant constant diagram. That step requires its own replacement argument.

## 3. Marked terminal vertices: a separate repair to test

Mark a simplex's terminal vertex by a map from the singleton (i). Require
morphisms to preserve this marking. The resulting category is a full
subcategory of the **under category of the singleton**, rather than a full
subcategory of Δ′I. A map selecting an earlier repeated copy of i is excluded.

This category has an initial marked singleton and is direct. Those facts,
and the fact that the forgotten chain ends at i, are checked in
`ResolutionTerminalVertex.lean`.

`ReedyConstantInitial.lean` proves that a constant diagram at a cofibrant
object is Reedy cofibrant on any direct category with an actual initial object.
The marked category therefore supports the constant-diagram part of the proof,
including the natural map from the marked singleton diagram.

There is now a checked obstruction to the simplest continuation:
`terminalVertexForget_not_final` in `TerminalVertexCofinalityObstruction.lean`
proves that its forgetful functor to Δ′I is not final. In the comma category
under the singleton, the assertion “this map selects the marked vertex” is
invariant under every morphism. The two endpoint inclusions into the constant
edge lie on different sides of this invariant. The comma category is therefore
not connected. When I is terminal, Δ′I is the whole original fiber, so even
that case rules out the naive ordinary-cofinality repair.

This does not refute a comparison restricted to suitable homotopical diagrams.
Such a comparison and the required Reedy restriction theorem remain to be
proved. Initiality alone does not complete Proposition 9.5.4. This construction
is our attempted correction; it is not attributed to the paper.

## 4. Categorical subdivision and a poset replacement

Del Hoyo constructs a subdivision functor Sd on small categories and a natural
augmentation ε : Sd(I) → I. Its objects are nondegenerate chains; morphisms use
a quotient relation, not just the literal face maps between all chains.
Theorem 21 states that Sd²(I) is a poset, and Theorem 32 proves that ε induces
a weak equivalence of classifying spaces. See
[*On the subdivision of small categories*, arXiv:0707.1718v2](https://math.uchicago.edu/~may/FINITE/ArgentinianPapers/DelHoya.pdf).

This is a promising route when a poset index is preferable. The poset is not
generally directed: arbitrary classifying-space homotopy types must remain
possible. Before using it for arbitrary diagram homotopy colimits, inspect the
augmentation's comma categories and prove the comparison in the necessary
direction. The classifying-space statement quoted here is not being promoted
to an unproved general homotopy-colimit formula.

## 5. Simplicial replacement and the bar construction

In the spaces/model-category setting, replace a diagram by a simplicial object
whose terms are coproducts indexed by composable chains. Its realization
computes a homotopy colimit under the appropriate cofibrancy assumptions.
This reorganizes the calculation into coproducts and a realization. It does
not itself replace I by a filtered category.

Dugger's [*A Primer on Homotopy Colimits*](https://pages.uoregon.edu/ddugger/hocolim.pdf),
§§4 and 11, explains simplicial replacement and the two-sided bar construction.
Example 21.2 permits discarding degeneracies for a full simplicial index via
a homotopy-cofinality argument. The resulting face-only simplicial index has
the **inverse** orientation; it must not be confused with Δ′I as a direct
category. Example 21.6 warns that the same assertion fails for truncated
simplicial indexing categories.

A formalization in our ABC setup must construct the required realization or
frame objects from the available axioms, rather than assume simplicial tensors
or a model-category structure.

## 6. Bounded diagrams on the nerve

Chachólski–Scherer develop model approximations using bounded diagrams on the
simplex category of a nerve. Degeneracy maps are required to act by
isomorphisms. Their Bousfield–Kan approximation for arbitrary small I is
Theorem 15.1; Lemma 15.2 is the terminal-object comparison, proved later as
Corollary 23.6. See
[*Homotopy theory of diagrams*, arXiv:math/0110316](https://arxiv.org/pdf/math/0110316).

This offers an older route with an explicit terminal comparison worth auditing
against the gap in §9.5. It uses model approximations and bounded diagrams,
which differ from our restricted semisimplicial ABC diagrams. It is a related
reduction technique, not yet a checked ABC theorem in this repository.

## 7. Directed posets when the input is already filtered

The [Stacks Project, Lemma 4.21.5, tag 0032](https://stacks.math.columbia.edu/tag/0032)
constructs a cofinal directed-poset system for a filtered index category and
proves the resulting ordinary colimit comparisons. This is the right setting
for a genuine “replace by a directed set” theorem.

For a homotopy-colimit application, also show that the comma categories of
the replacement are filtered, hence weakly contractible. This extra step must
be checked for the selected construction; an arbitrary final functor need
not have contractible comma nerves. No assertion here extends the theorem
to a nonfiltered input category.

## Reference dependencies and differences from the main paper

The first route implements the main paper's resolution, but rejects the false
initial-object argument. Routes 2 and 3 are to be developed separately, with
their comparison theorems stated explicitly. The other routes are alternatives
or related tools with their own hypotheses and are not claimed as formalized.

Lenz, [*Homotopy (pre)derivators of cofibration categories and quasicategories*,
Proposition 3.1](https://msp.org/agt/2018/18-6/agt-v18-n6-p12-p.pdf), cites either
Rădulescu-Banu 9.5.8 or Cisinski 6.17 and 2.5 for a direct-resolution equivalence.
However, [Cisinski, *Catégories dérivables*, Lemma 6.15](https://www.numdam.org/item/BSMF_2010__138_3_317_0.pdf)
refers back to Rădulescu-Banu 9.5.4. This reference chain is not an independent
repair of the proof under discussion. The literature search has not located
an explicit published correction of Lemma 9.5.2; that is a search limitation,
not a historical claim that nobody noticed it.

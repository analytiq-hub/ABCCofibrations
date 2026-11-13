# Relative colimits of Reedy cofibrant diagrams

`ReedyKan.lean` formalizes a finite case of Theorem 9.4.2(1) of
Rădulescu-Banu's *Cofibrations in Homotopy Theory* (math/0610009v4).

The ambient category is an `ABCPrecofibrationCategory`: only CF1–CF4 are
assumed. The source indexing category is finite and direct. For preservation
of maps, both indexing categories have finite hom-sets; the existence and
cofibrancy statement does not require the source finite-hom hypothesis.
In particular, the target finite-hom assumption is needed even when the
source has finitely many objects: objects of the comma category over `d`
include choices of arrows `u(e) ⟶ d`.

The proof restricts a Reedy cofibrant diagram to each comma category. Its
latching categories are equivalent to the corresponding source latching
categories. The finite Reedy colimit theorem then gives existence,
cofibrancy, and preservation of cofibrations and weak equivalences between
Reedy cofibrant diagrams.

`KanMapComparison.lean` defines `pointwiseLeftKanMap` using the universal
property of the two individual Kan extensions. It does not require Kan
extensions of every diagram. The unit equation characterizes its action;
`pointwiseLeftKanMap_app` identifies each component with the comma-colimit
map, conjugated by mathlib's canonical comparison isomorphisms.
Consequently `reedyCofibration_pointwiseLeftKanMap` and
`reedyCofibrant_pointwiseLeftKanMap_weakEquivalence` concern actual maps
between the chosen Kan extensions.

Differences from the paper: this is a finite specialization, with the
additional target finite-hom assumption, rather than the full direct-category
theorem using CF5–CF6. The proof uses the finite Reedy colimit theorem and
mathlib's chosen Kan extensions and comparison isomorphisms. We use mathlib's
standard name “left Kan extension” for relative colimits; the paper's Kan
terminology is discussed in [the earlier note](adjunctions-kan-abelian.md).
`ReedyRightKan.lean` now proves the finite inverse/right Kan statement
9.4.2(2)(a)–(c) by applying the cofibration theorems to opposite categories.
`KanOpposite.lean` proves the generic universal-property bridge, existence
of pointwise right extensions, and the natural comparison isomorphism with
the unopposite left extensions. The fibration and weak-equivalence statements
are about canonical maps between mathlib's chosen right extensions. The
assumptions are the dual ones (F1–F4 and finite source, with finite hom-sets
as above). The full infinite cases remain unfinished; the finite-truncation extension is described below.


## Pointwise diagram structures

`PointwiseCofibrationCategory.lean` completes CF5–CF6 for the pointwise
structure on finite direct diagrams (Theorem 9.2.4(1)(b)). Cofibrant diagrams
are precisely the pointwise cofibrant diagrams. Coproducts of such families,
and sequential colimits of pointwise cofibrations starting cofibrantly,
exist by evaluating in the ambient cofibration category. Evaluation preserves
these particular colimits. The comparison isomorphisms identify their maps
with ambient coproduct maps and sequential structure maps.

The finite inverse version, 9.2.4(2)(b), transports the entire cofibration
category structure along the equivalence with opposite diagrams. Products
and inverse sequences are therefore proved by duality. This does not yet
establish CF5–CF6 for the Reedy structures.

Differences from the paper: the indexing category still has finitely many
objects and finite hom-sets, because the available factorization proof for
CF4 uses that restriction. CF5 and CF6 themselves are checked pointwise;
no assumption that the ambient category has all colimits is introduced.

## Relative colimits and limits

`ReedyOpen.lean` represents an open full subcategory by an object property
closed under taking sources of arrows. Restriction preserves latching
objects up to equivalence, Reedy cofibrancy, and Reedy cofibrations. The
earlier maximal-object complement restriction is now a specialization of
this construction. `ColimitComparison.lean` shares the categorical
comparison machinery, independently of the homotopical axioms.

`ReedyRelativeColimits.lean` proves 9.4.1(1)(a)–(c) for open full subcategories
of finite direct categories. Part (a) needs only finitely many objects;
(b) and (c) also require finite hom-sets. The canonical comparison in (b)
and (c) is `relativeColimMap`: from the pushout of the ambient source
colimit and the restricted target colimit to the ambient target colimit.
The colimits exist by (a); the map statements accept these colimits as
instance hypotheses and supply the required pushout.

`ReedyRelativeLimits.lean` proves 9.4.1(2)(a)–(c) with the dual hypotheses.
These are native limit and pullback statements. `LimitComparison.lean`
identifies their restriction maps and relative comparisons with opposite
colimit maps, so the fibration arguments reuse the cofibration results.

Differences from the paper: these are finite specializations using only
CF1–CF4 or F1–F4. The induction removes maximal objects outside the open
subcategory. The cofibration comparison uses the existing gluing and
pushout-composition lemmas. The weak-equivalence comparison follows from
excision and the absolute colimit theorem. The paper's infinite construction
is not implemented here. The public subcategory formulation uses literal
full subcategories; the induction also handles fully faithful functors
whose object image is closed under predecessors.

## Kan extensions preserve Reedy structures

`ReedyKanBoundary.lean` constructs the open boundary of the comma category:
objects `u(e) ⟶ d` for which `u(e) ≠ d`. The boundary colimit exists and is
cofibrant, and its map into the full comma colimit is a cofibration.

`KanLatchingComparison.lean` proves that this boundary colimit is a latching
object of the left Kan extension. It constructs the cocone directly from
the individual comma colimits, proves its universal property, and identifies
its latching map. The comparison is natural in maps of source diagrams.
`ReedyKanReedy.lean` uses it to prove 9.4.3(1)(a)–(c).
`ReedyRightKanReedy.lean` transports these results to the native chosen
right Kan extensions, proving the finite version of 9.4.3(2)(a)–(c).

Differences from the paper: the source has finitely many objects and the
target has finite hom-sets; (b) and (c) additionally use finite source
hom-sets. Both indexing categories are direct, or inverse in the dual case.
Only the four pre(co)fibration axioms are used. The latching comparison uses
a direct cocone proof instead of the paper's Grothendieck construction and
iterated-colimit argument. Part (c) reuses 9.4.2(c), as in the paper. No
infinite case or Reedy CF5–CF6 result is claimed.

## Unbounded diagrams with finite degree truncations

`DegreeColimits.lean` constructs the sequence of colimits over the full
subcategories of objects with degree less than `n`. It proves directly that
the sequential colimit of those colimits is a colimit of the whole diagram,
and proves naturality in maps of diagrams. This categorical reconstruction
assumes only the individual colimits involved.

`ReedyDegreeColimits.lean` proves 9.3.5(1)(a)–(c) for possibly infinite
direct categories whose bounded-degree truncations have finitely many
objects. The open-restriction theorem supplies Reedy cofibrant truncations;
the finite relative theorem makes their colimits a sequence of cofibrations.
CF6 then gives the whole colimit. For (b), the finite relative comparisons
form a Reedy cofibration of sequences. The new
`cofibration_colimMap_of_reedy` in `SequentialColimits.lean` handles that
step using the same pushout-sequence construction as the existing
weak-equivalence argument. Part (c) uses the existing weak-equivalence
theorem for sequences.

`ReedyDegreeLimits.lean` proves the native limit versions 9.3.5(2)(a)–(c)
by duality. Its degree function decreases along nonidentity arrows of the
native inverse category. Its bounded-degree subcategories have finitely
many objects, just as on the direct side.

Differences from the paper: this is an unbounded special case of the
absolute colimit/limit theorem, with a finite-object assumption on every
bounded-degree truncation. Parts (a) and (b) use CF1–CF4 plus CF6(1), or
their duals; (c) additionally uses CF6(2). Parts (b) and (c) retain the
finite-hom assumption of the finite map theorems. CF5 and F5 are not used.
This does not supply the full infinite relative-colimit or Kan-extension
theorems. The arbitrary-layer construction is now implemented separately; see below.


## Arbitrary small diagrams

The finite restrictions above describe the earlier CF1–CF4 results and
remain appropriate for those APIs. The new
[arbitrary-layer note](reedy-arbitrary-layers.md) records the full
9.3.5(1)–(2)(a–c) and 9.4.2(1)–(2)(a–c), using CF5/CF6 and their duals.
`ReedySmallKan.lean` and `ReedySmallRightKan.lean` impose no finite-object
or finite-hom assumptions. Their target indexing category is arbitrary
small. The relative filtration now proves 9.4.1(a),(c), and the same boundary
comparison gives 9.4.3(a),(c), on both sides. Their map statement (b)
still needs the relative sequential comparison described in that note.

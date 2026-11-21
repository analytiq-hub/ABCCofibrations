# Full small diagram categories — Theorem 9.2.4

Theorem 9.2.4(1)–(2)(a),(b) of *Cofibrations in Homotopy Theory*,
math/0610009v4, is implemented for arbitrary small direct and inverse indexing
categories. This completes the diagram-category axioms after the unrestricted
factorization and colimit results of §§9.3–9.4.

## Statements and assumptions

For a small direct category `D : Type w` and an ambient
`ABCCofibrationCategory.{w} M`, the library supplies low-priority instances:

- `ReedyDiagram.cofibrationCategory_small`: CF1–CF6 with Reedy cofibrations
  and pointwise weak equivalences.
- `PointwiseDiagram.cofibrationCategory_small`: CF1–CF6 with pointwise
  cofibrations and weak equivalences.

For a small inverse category and an ambient `ABCFibrationCategory.{w} M`,
the native theorems are:

- `ReedyFibDiagram.fibrationCategory_small`: F1–F6 with Reedy fibrations.
- `PointwiseFibDiagram.fibrationCategory_small`: F1–F6 with pointwise fibrations.

These inverse results transport the direct structures through
`Functor.opUnopEquiv`; they do not repeat the mathematical proofs. They are
structure-valued theorems, available for local installation, following the
existing native inverse interface. Weak equivalences remain pointwise.

There are no finite-object or finite-hom assumptions. The new full structures
use coproducts/products indexed in universe `w`, which also contains the
objects and arrows of `D`. Object and morphism universes of `M` remain separate.
The older finite pointwise instances retain their arbitrary coproduct universe.
More generally, `PointwiseDiagram.cofibrationCategory_of_precofibrationCategory`
packages CF5–CF6 in any supplied coproduct universe, given the ambient full
structure and an existing pointwise CF1–CF4 structure. Its proof requires no
finiteness or directness assumptions.

## Latching objects and colimits

`PointwiseColimitInterchange.lean` proves a categorical interchange result
from individual colimits: a pointwise colimit cocone on a diagram of functors,
together with the colimits of each inner diagram and their outer diagram,
constructs a colimit cocone on the resulting functor.

`ReedyColimitInterchange.lean` applies this to restriction to the latching
category at an object `d`. The resulting isomorphism identifies the colimit of
the latching objects with the latching object of the colimit diagram. The
library checks its formulas on the colimit legs, its compatibility with the
latching maps, and naturality in a map of diagrams. The criterion
`reedy_colimit_at` transfers cofibrancy and the latching-map cofibration through
these isomorphisms.

Only the particular colimits in these statements are assumed or constructed.
The ambient category need not have all colimits of either shape.

## Coproduct axiom CF5

`DiscreteColimitCofibrations.lean` converts the ambient coproduct axiom into
statements about any chosen colimit of a discrete diagram. This avoids
assuming a particular presentation of a coproduct.

`ReedyCoproducts.lean` first constructs coproducts of Reedy cofibrant diagrams.
At each object, the latching comparison identifies the new latching map with
the coproduct of the original latching maps. Ambient CF5 supplies its
cofibration and the cofibrancy of its source.

For a family of Reedy cofibrations, take the coproduct of their relative
latching pushout squares. The pointwise pushout-colimit comparison identifies
this with the relative latching square of the coproduct map. Its comparison
map is a coproduct of cofibrations, followed by the evaluation isomorphism.
This proves `reedyCofibration_coproduct`. This argument itself needs no
directness assumption once all the specified Reedy data are supplied.

The trivial-cofibration clause reuses the pointwise CF5 theorem. It uses the
previously proved fact that Reedy cofibrations are pointwise cofibrations.

## Sequential axiom CF6

`ReedySequentialColimits.lean` constructs the sequential colimit pointwise.
At every object, its latching objects form a sequence of cofibrations. The
relative Reedy conditions on the original sequence give exactly the relative
pushout hypotheses needed for `cofibration_colimMap_of_reedy` applied to the
sequence of latching maps.

The interchange theorem therefore proves that the colimit diagram is Reedy
cofibrant. The first-stage sequential pushout comparison proves that its
initial leg is a Reedy cofibration. These are packaged in
`ReedyDiagram.sequentialCofibrationAxiom_small`. The trivial clause
`ReedyDiagram.trivialSequentialAxiom_small` follows from ambient CF6 pointwise,
using evaluation's colimit comparison.

`ReedyCofibrationCategory.lean` assembles these results with the earlier
CF1–CF4 instance. `SmallReedyFibrationCategory.lean` transports the full
structure to the native inverse category.

## Differences from the paper

The mathematical statements agree with Theorem 9.2.4, with explicit universe
bounds as above. The proof expands the paper's interchange of colimits into
chosen cocones and their universal properties. This restricted construction
avoids the global shape-cocompleteness assumptions of mathlib's general
chosen-colimit Fubini interface.

The sequential proof reuses the library's checked relative sequential
comparison rather than repeating its pushout argument. The pointwise CF5–CF6
proof is factored out from the earlier finite instance and reused unchanged.
The inverse cases are transported by categorical duality, with explicit
identifications of the native distinguished morphism classes. No functorial
factorization, stronger ambient cocompleteness, or additional axioms are used.

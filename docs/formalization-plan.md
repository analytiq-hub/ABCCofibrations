# ABC cofibration categories: formalization plan

## Goal and source

Formalize the theory of Anderson–Brown–Cisinski cofibration categories in Lean,
one small, verified increment at a time.

The reference used by this repository is Andrei Rădulescu-Banu,
[*Cofibrations in Homotopy Theory*, arXiv:math/0610009v4](https://arxiv.org/abs/math/0610009v4).
Use this version for definition and theorem numbers. This roadmap is provisional:
check each statement and its dependencies in the paper before implementing it.

The initial target is Chapter 1. Later milestones outline a route toward homotopy
colimits; they are not commitments to implement the whole paper in one pass.

## Current baseline

As inspected on 2026-11-07:

- `ABCCofibrations/Basic.lean` defines `ABCPrecofibrationCategory` (CF1–CF4)
  and `ABCCofibrationCategory` (CF1–CF6), following Definition 1.1.1.
- These classes use mathlib's cofibrations, weak equivalences, and cofibrant
  objects. Initial objects are supplied separately; the coproduct indexing
  universe is explicit.
- Existing results include preservation of cofibrancy by cofibrations,
  existence of cofibrant replacements, existence of target coproducts, and
  cofibrancy of sequential colimits.
- `ABCCofibrations/Examples.lean` checks the axioms on types with all maps in
  both distinguished classes.
- The project pins Lean and mathlib to `v4.36.0-rc2`.

The baseline `lake build` passed on 2026-11-07. The audit of correspondence
with the paper was completed on 2026-11-09 ([axiom-correspondence.md](axiom-correspondence.md)).

## Working method

For each increment:

1. Select one definition or a small group of closely related lemmas.
2. Record the paper reference, precise hypotheses, and prerequisite results.
3. Search mathlib and this project for reusable definitions and proofs.
4. State the Lean result with the weakest appropriate assumptions. Distinguish
   CF1–CF4 arguments from those requiring CF5 or CF6.
5. Implement and run `lake build`; resolve errors before marking the item done.
6. Update this plan with the declaration names and any mathematical or universe
   issues discovered along the way.

A completed increment has a proof without `sorry` or added axioms, a documented
source correspondence, and a successful build. A definition-only increment should
include a useful construction or application that exercises its interface.
Keep unfinished statements in planning notes rather than importing placeholders
into the library.

## Milestone 0 — Audit the foundations

- [x] Compare every field of the existing classes with Definition 1.1.1.
  Record a field-to-axiom correspondence, including which clauses are derived.
- [x] Check cofibrancy hypotheses, the scope of CF5, and the sequential diagrams
  used for CF6. Check empty families and universe restrictions explicitly.
- [x] Review interaction with mathlib's morphism-property instances; avoid
  overlapping instances and unnecessary global choices.
- [x] Build the existing library and record the baseline result.

**Complete (2026-11-09).** See [axiom-correspondence.md](axiom-correspondence.md).
The classes are equivalent to Definition 1.1.1; no definition changed. New
checked results in `Basic.lean`: `isCofibrant_iff_of_isInitial`,
`isCofibrant_coproduct_of_isEmpty`, `isCofibrant_obj_of_sequence`,
`cofibration_map_of_le`, `weakEquivalence_map_of_le`, `cf5_existence_iff`,
`isCofibrant_of_isColimit`, `cofibration_of_isColimit`,
`weakEquivalence_of_isColimit`, `sequential_cofibration_of_isColimit`, and
`sequential_weakEquivalence_of_isColimit`. Remaining, moved to §1.6: transfer
of CF5 to index types that are only `Small.{w}`.

Deliverable: a trustworthy foundation and a short correspondence note in `docs/`.
Change the current definitions only when this review identifies a concrete issue.

## Milestone 1 — Elementary API and finite coproducts

The finite-family results of Lemma 1.2.1(1) are implemented in
`ABCCofibrations/Coproducts.lean`; see the detailed work packages below.
The broader elementary API review remains open.

- [ ] Add convenient lemmas for identities, composition, isomorphisms, and
  two-out-of-three where existing mathlib interfaces do not already suffice.
- [ ] Expose pushout constructions and their cofibration/trivial-cofibration
  properties without requiring callers to invoke class fields repeatedly.
- [x] Develop finite coproducts of cofibrant objects from CF1–CF4, using the
  relevant results in §1.2 rather than assuming CF5.
- [x] Prove the corresponding elementary properties of coproduct inclusions
  and maps, with the paper's hypotheses checked individually.

Suggested module: `ABCCofibrations/Coproducts.lean`. Keep genuinely foundational
lemmas in `Basic.lean`; avoid splitting files until there is a coherent API.

## Early work packages

Each row is intended to be a separate, reviewable increment. Proposed declaration
names may change to fit mathlib conventions. Completed declarations below are in
the `ABCCofibrations.ABCPrecofibrationCategory` namespace.

### A. Foundation audit and interface decisions

- [x] Run the baseline build: `lake build` passed on 2026-11-07.
- [x] Create `docs/axiom-correspondence.md`, mapping every field to Definition
  1.1.1 and explaining the separately supplied category structures and initial
  object. For clauses represented by derived results, cite those declarations.
- [x] Check that the converse presentation of CF5 follows using identities,
  and document how target cofibrancy is derived from composition
  (`cf5_existence_iff`, `cofibrant_target`).
- [x] Check universe behavior on empty, finite, and countable indexing types.
  Distinguish the natural-number diagram category from the coproduct universe
  (`isCofibrant_coproduct_of_isEmpty`; finite case in `Coproducts.lean`).
- [x] Review transport to another chosen initial object and to isomorphic
  representatives of the colimits used in the axioms
  (`isCofibrant_iff_of_isInitial`, the `…_of_isColimit` theorems).

Interface decision already established by inspection: mathlib's coproduct
inclusion instances in `ModelCategory/IsCofibrant.lean` require unrestricted
`IsStableUnderCobaseChange`. Our CF3 has cofibrancy hypotheses, so use its
restricted square lemmas directly. Do not install the stronger instance.
Likewise, do not assert unrestricted `ContainsIdentities` or `RespectsIso` for
cofibrations without a separate justification covering noncofibrant sources.

Completion criterion: every axiom clause has a recorded correspondence, with
any discrepancy fixed and checked by a build. Met on 2026-11-09; no
discrepancy was found.

### B. Binary coproduct foundation — implemented

Source target: the binary construction used in Lemma 1.2.1(1).

| Declaration | Interface provided |
| --- | --- |
| `hasBinaryCoproduct` | Existence for two cofibrant objects |
| `cofibration_coprod_inl` | Left inclusion |
| `cofibration_coprod_inr` | Right inclusion |
| `coprod_cofibrant` | Cofibrancy of the chosen coproduct |
| `cofibration_coprod_map_id` | Cofibration after adding a fixed cofibrant summand |
| `weakEquivalence_coprod_map_id` | Weak equivalence for the corresponding trivial cofibration |

All six results use CF1–CF4 only. Existence is an explicit theorem: callers can
install it locally with `let := hasBinaryCoproduct A B`. The remaining results
accept existing coproduct instances, so they apply to the caller's chosen
coproduct. No global existence or cofibration instances are introduced.

Reused categorical infrastructure:

- `isCoproductOfIsInitialIsPushout` converts a pushout cocone to a binary cofan.
- `IsPushout.of_hasBinaryCoproduct'` supplies the inclusion square.
- `IsPushout.of_coprod_inl_with_id` supplies the square for a map with a fixed
  summand; its flipped orientation matches the CF3 interface.

### C. Finish the binary map API — implemented

Completed declarations: `cofibration_coprod_id_map`,
`weakEquivalence_coprod_id_map`, `cofibration_coprod_map`, and
`weakEquivalence_coprod_map`. A private universal-property proof supplies the
fixed-left-summand pushout square. The general results construct the intermediate
coproduct locally and derive its target summand's cofibrancy from the input map.
The following steps describe the completed construction.

1. Obtain the fixed-left-summand analogues of the two map lemmas. Compare a
   direct universal-property proof of the square with transport by coproduct
   symmetry; choose the shorter proof that preserves the hypotheses.
2. Factor `coprod.map f g` through the intermediate coproduct with one target
   summand. Supply its existence and cofibrancy locally.
3. Prove `cofibration_coprod_map`, then `weakEquivalence_coprod_map` when both
   component maps are trivial cofibrations. Use mathlib's existing composition
   and weak-equivalence API rather than adding duplicate lemmas.

Completion criterion: the two-map results compile under
`ABCPrecofibrationCategory`, without CF5, general coproducts, or unrestricted
pushout stability. Handle targets by deriving their cofibrancy from the input
cofibrations, rather than requiring redundant assumptions.

### D. Pass from binary to finite families — implemented

Existence and cofibrancy are implemented for `Fin n` via `hasCoproduct_fin`
and `coproduct_fin_cofibrant`. Their shared induction uses mathlib's
`extendCofanIsColimit`, with the initial object as the empty case. Cofibrancy
is transported to the caller's chosen coproduct by the unique colimit
isomorphism. The map properties are implemented as
`cofibration_coproduct_map_fin` and `weakEquivalence_coproduct_map_fin`.
Their shared induction handles the empty map as an isomorphism, and compares
each successor coproduct with the binary coproduct of its head and tail.

The public results for an arbitrary `[Finite ι]` are:

| Declaration | Conclusion |
| --- | --- |
| `hasCoproduct_finite` | Existence for a cofibrant family |
| `coproduct_finite_cofibrant` | Cofibrancy of any chosen coproduct |
| `cofibration_coproduct_map_finite` | Preservation of cofibrations |
| `weakEquivalence_coproduct_map_finite` | Preservation of trivial cofibrations |

These use a locally chosen equivalence with `Fin n` and mathlib's
`Sigma.reindex`. No enumeration is exposed in the statement. The indexing
universe is independent of the object and morphism universes. Together these
results cover Lemma 1.2.1(1); they introduce no global instances.
The following steps describe the completed construction.

1. Start with `Fin n`-indexed families. Check mathlib's existing decomposition
   of a coproduct indexed by `Fin (n + 1)` before introducing recursion.
2. Treat `n = 0` using the initial object. Record how the unique map between
   empty coproducts is identified with an isomorphism.
3. Prove existence and cofibrancy by induction, then prove preservation of
   cofibrations and trivial cofibrations using package C.
4. Transport to an arbitrary finite indexing type through an equivalence with
   `Fin n`, reusing mathlib reindexing isomorphisms.

Completion criterion: cover the cofibration side of Lemma 1.2.1, including the
empty family, without strengthening the category assumptions. Do not mark the
whole finite-coproduct milestone complete after only the binary case.

### E. Factorization increments — basic Brown and relative factorization implemented

`Factorization.lean` now proves `exists_brown_factorization` (Lemma 1.3.1(1))
and `exists_brown_factorization_with_coprod` (Remark 1.3.2). Both expose the
intermediate cofibrant object, the three maps, their morphism properties, and
the two factorization/section equations. The basic theorem constructs a
coproduct instance locally; the stronger theorem works with the caller's
chosen coproduct and retains its combined map as a cofibration.
No factorization data structure or global choice was needed.

Completed implementation tasks:

1. Write an existential statement exposing the intermediate object, the three
   maps, and all equations in Lean composition order.
2. Apply the existing CF4 field to `coprod.desc f (𝟙 B)`.
3. Derive the properties of its restrictions using package B and mathlib's
   two-out-of-three lemmas. Keep the stronger coproduct-map property available
   for the later relative construction.
4. Decide whether a data structure improves actual downstream use only after
   writing the existential theorem; avoid choosing factorizations globally.

The next separate increment, Lemma 1.3.3(1), is also implemented as
`exists_relative_factorization`. Its input is a commutative square and a
specified cofibration/weak-equivalence factorization of its top map. Only the
two left-hand objects are required to be cofibrant. Its output includes:

- The new cofibrant factorization object, its cofibration and weak-equivalence
  factors, and their factorization equation.
- A map between the factorization objects making both squares commute.
- A cofibration `k` from `pushout i₁ a`, with both equations identifying it as
  the canonical pushout comparison map.

The proof uses restricted CF3 to make the pushout cofibrant and CF4 to factor
the induced map out of it. It makes no functorial choices and imposes no
cofibration hypothesis on the left vertical map.

The attempt at Lemma 1.3.4(1) identified an obstruction to its separate
pushout-comparison claims for arbitrary vertical maps. See
[relative-brown-factorization.md](relative-brown-factorization.md) for the
explicit finite-set example, its checked injectivity contradiction, and the
precise scope of the formal verification.

`exists_compatible_brown_factorization` now proves compatibility of the two
Brown factorizations and a cofibration for the combined relative pushout
comparison. This is the corrected statement of the note: the original
separate-comparison claims are false by the checked counterexample, so they
are not formalized and must not be used. No further work on 1.3.4(1) is
planned.

### F. Extension and cylinder entry point

The gluing lemma, Lemma 1.4.1(1), is now proved in `Gluing.lean`:
`gluing_cofibration` proves part (a), and `gluing_weakEquivalence` proves part
(b) for arbitrary weak equivalences on the three span vertices.

The dependency audit of the gluing proof is complete. Its proof order is:

1. Pushout pasting identifies the rear comparison as a cobase change of the
   front comparison.
2. CF3 gives the cofibration assertion and the weak-equivalence case with
   extra cofibration hypotheses.
3. `exists_relative_brown_of_cofibration_edges` supplies both separate Brown
   comparisons when the two edges are cofibrations, using two pushouts and CF4.
4. Brown replacement on the central vertex, the restricted construction along
   the cofibration edges, and compatible replacement on the other edges give
   an intermediate span. Applying step 2 to its two inclusion maps and using
   their common retraction proves the general case by two-out-of-three.

This proof uses CF1–CF4 and does not assume the invalid unrestricted comparison
claims. The theorem accepts arbitrary `IsPushout` representatives of both faces.
The front and rear comparisons in part (a) use chosen pushouts, whose existence
follows from CF3.

Excision, Lemma 1.4.2(1), is now proved in `Extension.lean` as
`weakEquivalence_of_isPushout_of_cofibration`; `weakEquivalence_pushout_inl`
specializes it to the canonical pushout. The proof applies gluing to a cube
with identity maps on two vertices. Lemma 1.4.3's comparison of alternative
axiom systems remains outstanding.

For §1.5, the existing mathlib `Cylinder` and `Cylinder.IsGood` interfaces have
been reused in `Cylinder.lean`. The paper's Definition 1.5.1(1) corresponds to
a good cylinder on a cofibrant object. `exists_good_cylinder` proves Lemma
1.5.2(1). The endpoint cofibration and weak-equivalence lemmas, together with
`cylinder_cofibrant`, provide the elementary consequences following that lemma.
The endpoint weak-equivalence results apply to every mathlib cylinder.

Lemma 1.5.3(1) is implemented as `exists_relative_good_cylinder`, applying
Lemma 1.3.3(1) to the square of codiagonals. Its witnesses retain both endpoint
equations, the projection equation, and the cofibration from the relative
pushout, with its two defining equations. It works with chosen endpoint
coproducts and a chosen relative pushout; existence of these follows from the
coproduct API and CF3. It does not depend on Lemma 1.3.4.

The elementary constructions for working with homotopies have also begun:
`good_cylinder_symm` proves goodness after reversing the endpoints, and
`cylinder_trans` with `good_cylinder_trans` concatenates good cylinders by
gluing their adjacent endpoints. These use restricted CF3 and pushout pasting,
without model-category axioms. `exists_common_cylinder_refinement` also provides
a common cylinder refinement by trivial cofibrations, as used in §6.3.

`LeftHomotopy.lean` reuses mathlib's `Cylinder.LeftHomotopy` data and defines
two distinct relations: `StrictLeftHomotopyRel` and `LeftHomotopyRel`. The latter
allows a trivial cofibration of the target, as required by the paper's §6.3.
Both are proved reflexive, symmetric, and transitive. Change of cylinder
(`LeftHomotopyRel.exists_on_cylinder`, Lemma 6.3.2(1)) uses common refinement
and a pushout of the homotopy map. Relative cylinders then give precomposition
compatibility. Postcomposition and horizontal composition are also proved,
covering Theorem 6.3.3(1). No strict-homotopy precomposition claim is assumed.

`HomotopyCategory.lean` constructs the category `πₗ Mcof` described after
Theorem 6.3.3, as `LeftHomotopyCategory C`. It reuses mathlib's
`CofibrantObject C` and `CategoryTheory.Quotient`. The relation on the full
subcategory is proved to be a congruence. The quotient functor
`toLeftHomotopyCategory` is full, and `toLeftHomotopyCategory_map_eq_iff`
identifies equality of its images with left homotopy.

`StrictLeftHomotopyRel.weakEquivalence_iff` and
`LeftHomotopyRel.weakEquivalence_iff` prove invariance of weak equivalence.
This provides the quotient's `CategoryWithWeakEquivalences` instance, with
`weakEquivalence_toLeftHomotopyCategory_map_iff` checking it on representatives.
No model-category assumptions or general coproduct assumptions are introduced.

## Milestone 2 — Factorization and extension lemmas

- [ ] Translate the cofibration-side statements of §1.3 into a dependency list.
- [ ] Formalize the factorization lemmas in that order.
- [ ] Do the same for the extension lemmas of §1.4.
- [x] Prove both parts of the gluing lemma, Lemma 1.4.1(1), with a repaired proof.
- [x] Derive excision (Lemma 1.4.2(1)) from gluing.
- [ ] Extract reusable commutative-square and pushout lemmas when multiple proofs
  need them, reusing mathlib's universal-property interfaces.

Suggested modules: `Factorization.lean` and `Extension.lean`.
Keep existential factorizations as the default; introduce chosen data locally
when a construction needs it, without assuming functoriality.

## Milestone 3 — Cylinders and elementary homotopy

- [x] Define cylinder objects in a form compatible with §1.5 and mathlib's
  existing abstractions, after comparing the available interfaces.
- [x] Construct cylinders for cofibrant objects using the preceding milestones.
- [x] Construct relative cylinders (Lemma 1.5.3(1)) using relative factorization.
- [x] Reverse and concatenate good cylinders under CF1–CF4.
- [x] Introduce left homotopy and prove only the elementary properties justified
  by the available hypotheses.
- [x] Identify and defer claims that need the later homotopy-category theory.

Left homotopy is now identified with equality in localization of the full
subcategory of cofibrant objects and of the ambient category, proving
Theorem 6.3.1(1) under CF1–CF4.

Suggested module: `Cylinder.lean`. First deliverable: the cylinder existence
theorem, with its source statement and prerequisites documented.

## Milestone 4 — Complete the selected Chapter 1 foundations

- [ ] Develop the consequences of CF5 and CF6 in §1.6, including useful APIs for
  coproducts and sequential composites. **In progress:** Lemmas 1.6.2(1),
  1.6.3(1) (`SmallSums.lean`), 1.6.4(1) and 1.6.5(1)
  (`SequentialColimits.lean`) are proved; see
  [the §1.6 note](mathematics/cf5-cf6-consequences.md). The proof of 1.6.4(1)
  uses only the cofibration-edge relative Brown factorization
  `exists_relative_brown_of_cofibration_edges`, not the refuted separate
  claims of 1.3.4(1). Remaining: Lemma 1.6.1, `Small`-index transfer of CF5,
  and the fibration statements (which need F5–F6).
- [x] Treat over and under categories (§1.7), making object restrictions explicit.
  **Done:** Proposition 1.7.1 in full. The CF5–CF6 parts are in
  `OverUnderCofibrationCategory.lean`, and the F5–F6 parts follow by
  transport (`ABCFibrationCategory`). Proposition 1.7.1(1), CF1–CF4 part, is proved in
  `OverUnder.lean` for `Over A` and, with `A` cofibrant, `Under A`; see
  [the §1.7 note](mathematics/over-under.md). The F1–F4 part of the fibration
  statement (2) is proved in `OverUnderFibration.lean` by transport along
  mathlib's op-equivalences.
- [x] Formalize the properness results (§1.8) needed by subsequent work.
  **Done:** all of §1.8, both the cofibration statements (`Properness.lean`)
  and the fibration statements by duality (`RightProperness.lean`): PCF/PF,
  left/right proper maps, Theorem 1.8.4(a)–(d), and Propositions 1.8.5–1.8.7,
  with the stability facts the paper asserts. For 1.8.6–1.8.7 the paper's
  (co)completeness is replaced by the existence of the (co)limits used; see
  [the §1.8 note](mathematics/properness.md).
- [ ] Review Chapter 1 coverage and list any omitted statements with reasons.

Do not generalize sequential composites to arbitrary ordinal-indexed composites
without checking the additional argument and size requirements.

## Later milestones

Choose the order of these larger projects after the Chapter 1 APIs stabilize.

| Project | Entry point | First concrete deliverable |
| --- | --- | --- |
| Comparison and examples | Chapters 2–3 | A bridge from an appropriate mathlib model-category structure, or one nontrivial example |
| Localization and derived functors | Chapters 5–7 | A compatible homotopy-category interface using mathlib localization |
| Diagram categories | Chapter 9, starting with direct diagrams | Definitions and elementary constructions for the diagrams needed next |
| Homotopy colimits | Chapter 9 | A construction for a restricted diagram shape, followed by its stated universal property |
| Derivators | Chapter 10 | A precise inventory of missing categorical infrastructure before implementation |

Audit mathlib's existing category theory before adding infrastructure corresponding
to Chapters 4 and 8. Treat the dual fibration theory as a separate scope decision;
prefer transport through opposite categories where it faithfully matches the
statements.

## Immediate next increment

### Resume point (2026-11-09)

**Theorem 6.1.6 is complete:** `cofibrantLocalizationToAmbient` is an
equivalence. `ReplacementComparison.lean` supplies both inverse comparison
isomorphisms, a parameterized equivalence, and an equivalence with replacement
choices supplied by existence. The proof specializes to inclusion of cofibrant
objects and constructs an inverse directly, rather than formalizing the paper's
general approximation theorem. `cofibrantInclusion_comp_isLocalization` makes
restriction of any ambient localization a localization of cofibrant objects.
`ambient_map_eq_iff_cofibrant_leftHomotopy` now proves the full ambient
equality criterion of Theorem 6.4.4(1)(c).
**Theorems 6.4.4(1) and 6.4.5(1) are now complete:**
`AmbientHomotopyFractions.lean` states the ambient fraction representations
and equality criteria. `HomotopyFractions.lean` now also proves the general
weak-equivalence-denominator criterion, using the quotient's calculus of
fractions. The ambient equality iff left homotopy result also supplies 6.3.1(1).
**Theorem 6.2.1(1) is now complete:** `DerivedFunctor.lean` proves that
inclusion of cofibrant objects is a left derivability structure, then obtains
pointwise derived-functor existence and invertibility of any derived counit
at cofibrant objects. Composing the original functor with target localization
gives the paper's total left derived functor under the stated preservation
hypothesis. See [the derived-functor note](mathematics/derived-functors.md),
including its explicit comparison of universal-property conventions.
The latest increment computes any such derived functor on any cofibrant
replacement: `leftDerivedObjIsoOfCofibrantReplacement`, its counit equations,
and naturality for a commutative replacement square. Comparison isomorphisms
between two replacements agree with any map over the ambient object and
satisfy identity and composition laws. They require no functorial choice.
`DerivedFunctorComparison.lean` now compares any left derived functor with
the localization lift of its cofibrant restriction. It proves a necessary and
sufficient equivalence criterion and an existence theorem for derived
equivalences under that criterion. With explicit replacements, it also gives
the functor-level comparison with the reverse localization construction.
This is the categorical step of 6.2.3(1), not yet its full general
cofibrant-approximation formulation.
`DerivedEquivalence.lean` now expresses this criterion using
`cofibrantRestrictionLocalizerMorphism` and `IsLocalizedEquivalence`.
Brown's lemma constructs the morphism of localizers from preservation of
trivial cofibrations, assuming only two out of three for target weak
equivalences. Any total left derived functor is an equivalence exactly when
this restriction is a localized equivalence, and existence under that
condition is proved for arbitrary source and target localizations.
The latest increment, `CofibrantApproximation.lean`, formalizes Definition
6.1.1 (CFA1–CFA4), with the all-cofibrant source condition explicit in the
class. It proves cofibrancy of images, exact detection of weak equivalences,
object and arrow resolutions, common resolution extensions, and connectedness
of resolution categories. A localized equivalence is not assumed in the
class; it is now proved in `CofibrantApproximationLocalization.lean`. See [the approximation note](mathematics/cofibrant-approximations.md).
`CofibrantApproximationHomotopy.lean` now proves Lemma 6.1.3(1) for a
general approximation, with an explicit left-homotopy witness. It follows
the paper's boundary-factorization and cylinder-pushout construction,
using CFA3 only for a span of two cofibrations. Independence of fraction
choices (Lemma 6.1.4(1)) is now also proved, using common resolutions and
homotopy cancellation for both numerator and denominator.
`CofibrantApproximationFractions.lean` constructs fractions between
prescribed resolutions, proves independence and pushout composition, and
builds `resolutionFunctor`, which inverts ambient weak equivalences.
`CofibrantApproximationLocalization.lean` lifts it and proves both inverse
comparison isomorphisms, establishing Theorem 6.1.7(1) and the general
left derivability structure. `CofibrantApproximationDerived.lean` now proves
Theorem 6.2.2(1) under its full structural hypotheses, including invertibility
of any derived counit on the image of the approximation.
Theorem 6.2.3(1) is now also proved under its full structural hypothesis
in `DerivedApproximationEquivalence.lean`. `CofibrantSubcategory.lean` supplies
the restricted CF1–CF4 structure and the inclusion approximation instance.
`FibrationBasic.lean` starts the dual theory by transporting F1–F4 and
their elementary consequences through opposite categories.
`FibrantApproximation.lean` now transports the approximation localization
equivalence and right derivability structure and proves total right-derived
existence with invertible unit on image objects (6.2.2(2), with the weaker
composite preservation hypothesis). The fibrant-subcategory instances and
the native statements of 6.2.1(2) and 6.2.3(2) are now proved in
`FibrantSubcategory.lean` and `RightDerivedFunctor.lean`.
The derived functors now remain derived after arbitrary postcomposition.
`QuillenAdjunction.lean` applies the Maltsiniotis argument and proves
6.2.5(1), including joint existence. `QuillenComparison.lean` now proves
the comparison equations, full-faithfulness criteria in 6.2.5(2), and
the Quillen-equivalence conclusion in 6.2.5(3). `PathObject.lean` and
`RightHomotopy.lean` now start the native dual homotopy API; the explicit
opposite comparison, transitivity, postcomposition, and 6.3.1(2) are now
proved in `HomotopyOpposite.lean`. `RightHomotopyCancellation.lean`
transfers weak-equivalence cancellation, and `RightHomotopyFractions.lean`
proves right-fraction representation and common-denominator equality.
Different-denominator equality 6.4.4(2)(b) and both refinements in
6.4.5(2) are now proved as well. The native right-homotopy quotient, its weak-equivalence laws, the
equivalence with the opposite left quotient, and the right calculus of
fractions are now proved. `RightHomotopyLocalization.lean` now compares
the quotient localization with fibrant-object localization and ambient
localization, including the native inclusion equivalence 6.1.6(2).
Its direct comparison is now faithful, and equality in arbitrary
fibrant-object localizations is exactly right homotopy.

Suggested next construction:

1. **Complete with replacements as parameters:** choose a cofibrant replacement
   of each ambient object. For an ambient
   arrow, factor the coproduct of its composite with the source replacement
   and the target replacement. This supplies a fraction between replacements
   with a trivial-cofibration denominator.
2. **Complete:** use `weakEquivalence_fraction_map_eq_of_ambient_comparison` (or its
   trivial-cofibration version) to prove independence of the fraction choice.
   Prove the identity and composition laws to obtain a functor from the
   ambient category to the localization of cofibrant objects.
3. **Complete:** inversion, descent, and both inverse comparison isomorphisms
   establish the equivalence, with no functorial replacement assumption.
4. **Complete:** ambient fraction existence, both denominator equality criteria,
   and their correspondence with Theorems 6.3.1(1), 6.4.4(1), and 6.4.5(1).
5. **Complete:** mathlib's left derivability structure for the cofibrant
   inclusion, pointwise left derived-functor existence, invertible counit on
   cofibrant objects, and Theorem 6.2.1(1).
6. **Complete:** give an explicit computation isomorphism using any cofibrant
   replacement $Q A\xrightarrow{\sim}A$, for an arbitrary total left derived
   functor with its counit. Check naturality for a commutative square between
   replacements. Coherent comparisons between replacement computations are
   also complete.
7. **Complete:** compare an arbitrary left derived functor to the composite of
   `ambientLocalizationToCofibrant` with the localization lift of its
   restriction to cofibrant objects. The equivalence criterion and existence
   theorem under that criterion are also proved.
8. **Complete:** express the criterion using mathlib's
   `LocalizerMorphism.IsLocalizedEquivalence` for the cofibrant restriction
   of a functor between precofibration categories. Use Brown's lemma to
   obtain the required localizer morphism from preservation of trivial
   cofibrations.
9. **Complete:** formalize general cofibrant approximation functors (Definition
   6.1.1, CFA1–CFA4), using mathlib's functors, morphism properties, and
   preservation interfaces where appropriate. The source is a precofibration
   category with all objects cofibrant. Preserve the paper's restriction in
   CFA3 to pushouts whose two source maps are cofibrations. Elementary
   consequences, object and arrow resolutions, and connectedness of the
   resolution categories are also proved. The identity on an all-cofibrant
   precofibration category is a checked example.
10. **Complete:** prove that a general cofibrant approximation is a localized
    equivalence, Theorem 6.1.7(1). Cancellation, fraction independence,
    fractions between resolutions, and both inverse comparison isomorphisms
    give a direct proof. Only then apply mathlib's constructor to obtain
    the general left derivability structure; there is no circularity.
11. **Complete:** Theorem 6.2.2(1), with preservation required only after
    composition with the approximation. Brown's lemma is applied after
    target localization, so no target saturation hypothesis is added.
12. **Complete:** Theorem 6.2.3(1), including existence and the equivalence
    property for any total left derived functor. The cofibrant subcategory
    has its inherited CF1–CF4 structure, and its inclusion is a general
    cofibrant approximation.
13. **Complete:** prepare the dual fibration/right-derived infrastructure
    via opposite categories before the Quillen adjunction theorem 6.2.5.
    `FibrationBasic.lean` now defines F1–F4 as CF1–CF4 on the opposite and
    provides the native fibrancy bridge, terminal fibrancy, composition,
    two out of three, fibrant replacements, F4 factorization, and restricted
    F3 pullbacks. See [the duality note](mathematics/fibration-duality.md),
    including the difference from the paper's presentation.
    Fibrant approximations and right-derived existence are complete in
    `FibrantApproximation.lean`, including the unit computation on image
    objects. `FibrantSubcategory.lean` now packages its native subcategory
    and inclusion, and `RightDerivedFunctor.lean` proves 6.2.1(2) and
    6.2.3(2), including the unit and equivalence properties for any derived
    functor.
14. **Complete:** arbitrary postcomposition preserves the derived functors
    computed by these derivability structures (`DerivedAbsoluteness.lean`).
    `QuillenAdjunction.lean` records Definition 6.2.4(1)–(3) and proves
    Theorem 6.2.5(1) for arbitrary derived choices, plus joint existence.
    It uses mathlib's Maltsiniotis construction after proving its two
    postcomposition hypotheses. See [the adjunction note](mathematics/quillen-adjunctions.md).
15. **Complete:** the derived unit/counit and hom-set comparison formulas,
    both one-sided full-faithfulness criteria of 6.2.5(2), Definition
    6.2.4(4), and the derived-equivalence conclusion 6.2.5(3). These are
    in `QuillenComparison.lean`, with no weak-equivalence reflection
    assumption for localization.
16. **In progress:** the native path-object/right-homotopy interface is
    started in `PathObject.lean` and `RightHomotopy.lean`. Products of
    fibrant objects, good path objects, their trivial-fibration projections,
    reversal, and the strict/general right-homotopy definitions are proved,
    with reflexivity, symmetry, precomposition, and weak-equivalence
    invariance. The constructions use the native F3/F4 results already
    transported through opposites. See [the right-homotopy note](mathematics/right-homotopy.md).
    `HomotopyOpposite.lean` now compares arbitrary product/coproduct choices,
    proves goodness and homotopy equivalence under opposites, and transfers
    transitivity, postcomposition, and Theorem 6.3.1(2).
    Cancellation is now transported in `RightHomotopyCancellation.lean`.
    `RightHomotopyFractions.lean` proves 6.4.4(2)(a) with trivial-fibration
    denominators and a common-denominator equality criterion.
    The different-denominator criterion 6.4.4(2)(b) and both parts of
    6.4.5(2) are now transported, including arbitrary chosen product
    boundaries and exact denominator equality for trivial fibrations.
    The native quotient, its weak-equivalence laws, and its equivalence
    with the opposite left quotient are now proved. `RightHomotopyOre.lean`
    transports 6.4.3(2)(a) and supplies the right calculus of fractions,
    using cancellation for extensionality. Together with the prior
    cancellation results, 6.4.3(2) is complete.
    `RightHomotopyLocalization.lean` now proves those comparisons: the
    quotient has the strict localization universal property, localizing it
    agrees with localizing fibrant objects, and the native fibrant
    inclusion gives the ambient comparison (6.1.6(2)).
    Faithfulness and the equality criterion for arbitrary fibrant-object
    localizations are now proved: weak-equivalence classes are epimorphisms,
    so the right-calculus equality test cancels its denominator.
    **Complete:** native localization at trivial fibrations agrees with
    weak-equivalence localization. `BrownFibration.lean` transports the
    cofibrant Brown lemma across the opposite category, and
    `TrivialFibrationLocalization.lean` builds the equivalence of
    localizations, compatible with the canonical functors. The pullback
    Ore square converts a left fraction with trivial-fibration denominator
    into a right fraction; it is not yet a cancellation axiom.
    The relevant abstract right-calculus statement is Theorem 6.4.2
    (the earlier plan reference to 6.4.1(2) was imprecise). It is already
    installed for the native quotient, and is not claimed here for the
    trivial-fibration class.
    **Complete:** right-fraction representations in a localization of
    fibrant objects (`TrivialFibrationFractions.lean`): trivial-fibration
    denominators, common refinements, equality over a refinement,
    composition, finite common denominators, and fibration numerators with
    fibrant product boundary. Every result transports the corresponding
    statement of `TrivialCofibrationFractions.lean` through
    `fibrantObjectOpEquivalence`, using the general localization and
    fraction transport added to `FibrantOpposite.lean`.
    With this, the fibration-side localization theory of Chapter 6 mirrors
    the cofibration side. The foundation audit (Milestone 0) is now also
    complete. Chapter 1 §1.6 is in progress (Milestone 4).

No functorial factorization or functorial replacement is assumed. Connectedness
of replacement categories alone does not establish the comparison equivalence.
The cofibration proofs use CF1–CF4, and the dual fibration proofs use F1–F4. The latest full check is
`lake build ABCCofibrations`: 2228 jobs, without warnings. The accompanying
mathematical account is [cofibrant-replacements.md](cofibrant-replacements.md).
Local paper source for the next argument is
`references/radulescu-banu-2009/source/chap-homotopy.tex`, §6.4.
The [reference library](../references/README.md) contains fixed-version PDFs,
searchable text, unpacked arXiv sources where available, and provenance.
These are reading aids, not library dependencies.
The acquisition inventory is `references/inventory.md`: 70 PDFs with searchable
text and 54 unpacked source directories are available. It maps the broader
`docs/references.md` bibliography to local copies or missing-copy statuses,
and preserves the original v4 bibliography as an additional acquisition backlog.

### Completed infrastructure and remaining scope

The comparison functor is implemented. Current proof development is in the
localization project (Chapters 5–7), beyond the completed elementary homotopy
work of Milestone 3. Milestones 0, 1, 2, and 4 retain their unchecked items.

Completed localization infrastructure:

- `CofibrantApproximation.lean`: CFA1–CFA4 with all-cofibrant source, identity
  example, image cofibrancy, induced localizer morphism, object and arrow
  resolutions, common extensions, and connected resolution categories.
  The localized-equivalence consequence is proved in the module below.
- `LocalizationTransfer.lean`: shared categorical lemmas, used on both
  sides: a factorization of `W.Q` through a compatible quotient is a
  localization of the quotient, and two classes each inverted by the
  other's localization functor have the same localizations.
- `FibrantOpposite.lean`: the equivalence
  `(FibrantObject C)ᵒᵖ ≌ CofibrantObject Cᵒᵖ`, with definitional
  underlying-object/arrow equations, correspondence of weak equivalences,
  and of weak-equivalence-inverting functors; general transport of
  localizations and of right/left fractions for corresponding classes.
  Depends only on F1–F4.
- `RightHomotopyLocalization.lean`: quotient factorization and localization
  universal property; equivalences between quotient, fibrant-object, and
  ambient localizations; native inclusion comparison 6.1.6(2); faithfulness
  and the equality criterion for arbitrary fibrant-object localizations.
  The homotopy-inversion lemma is transported from the cofibration side.
- `BrownFibration.lean`: Brown's functor lemma on fibrant objects, by
  transport through the opposite precofibration category.
- `Properness.lean`: PCF, left proper maps, left properness of categories with
  all objects cofibrant, Theorem 1.8.4(1)(a)–(d) (including the precofibration
  structure of left proper maps), and Propositions 1.8.5(1)–1.8.7(1).
- `RightProperness.lean`: PF, right proper maps (defined in the opposite
  category, with pullback formulations), Theorem 1.8.4(2)(a)–(d), and
  Propositions 1.8.5(2)–1.8.7(2), by duality.
- `OverUnder.lean`: induced classes on `Under A` (generated by `to_dual` from
  mathlib's `Over` instances); Proposition 1.7.1(1), CF1–CF4 part, for
  `Over A` and for `Under A` with `A` cofibrant.
- `EquivalenceTransfer.lean`: transport of a precofibration structure along
  an equivalence of categories identifying cofibrations and weak equivalences.
- `OverUnderFibration.lean`: Proposition 1.7.1(2), F1–F4 part: `Under A` is a
  prefibration category, and so is `Over A` for fibrant `A`.
- `FibrationCategory.lean`: `ABCFibrationCategory` (F1–F6) as a cofibration
  category on the opposite category.
- `OverUnderCofibrationCategory.lean`: transfer of CF5–CF6 along forgetful
  functors and equivalences; coproducts in `Under A`; Proposition 1.7.1(1)
  for cofibration categories, and (in `OverUnderFibration.lean`) 1.7.1(2) for
  fibration categories.
- `ToDualRegistrations.lean`: temporary local `to_dual` dictionary entries
  (model-category classes, `MorphismProperty` cast, `Over ↔ Under`). Remove when
  mathlib registers these (after mathlib4#40940 and a `MorphismProperty`
  design for `to_dual`). When mathlib4#45324 (induced classes and model
  structure on `Under`) is merged and the pin updated, delete our generated
  `Under` instances in favour of mathlib's.
- `SequentialColimits.lean`: CF6(1)/(2) as standalone hypotheses; the
  Reedy step and Lemma 1.6.4(1) (colimits of degreewise weak equivalences of
  CF6 sequences), and Lemma 1.6.5(1) (equivalent forms of CF6(2)).
- `SmallSums.lean`: Lemmas 1.6.2(1) (finite and small sums of weak
  equivalences between cofibrant objects) and 1.6.3(1) (equivalent form of
  CF5), from one shared Brown-factorization argument.
- `TrivialFibrationFractions.lean`: right fractions with trivial-fibration
  denominators, common refinements and denominators, composition, and
  fibration numerators with product boundary, all transported from the
  cofibration side.
- `TrivialFibrationLocalization.lean`: equivalence of localization at
  trivial fibrations and at weak equivalences of fibrant objects, with
  compatible canonical functors, and the pullback Ore square for
  trivial-fibration fractions.
- `RightHomotopyCategory.lean`, `RightHomotopyWeakEquivalences.lean`: native
  quotient, exact equality relation, and descended weak-equivalence laws.
- `RightHomotopyCategoryOpposite.lean`: equivalence with the opposite left
  quotient, preserving and reflecting weak equivalences.
- `RightHomotopyOre.lean`: strict Ore squares and right calculus of fractions
  on the native quotient, using the earlier cancellation lemmas.
- `RightHomotopyCancellation.lean`: weak-equivalence cancellation on both
  sides of right homotopy, including the ambient precomposition variant.
- `RightHomotopyFractions.lean`: localized right-fraction representations
  with trivial-fibration denominators, general and sharpened equality
  criteria, and full product boundaries: all of 6.4.4(2)–6.4.5(2), together
  with the localization equality criterion from `HomotopyOpposite.lean`.
- `HomotopyOpposite.lean`: chosen-product/coproduct comparison, native
  path/cylinder and homotopy duality, transitivity, postcomposition, and
  the localization equality criterion 6.3.1(2).
- `PathObject.lean`: products of fibrant objects and good path objects,
  including trivial-fibration projections, fibrancy, and reversal.
- `RightHomotopy.lean`: native strict/general right homotopy, reflexivity,
  symmetry, precomposition, and weak-equivalence invariance.
- `QuillenComparison.lean`: comparison equations, Definition 6.2.4(4),
  both full-faithfulness criteria, and the Quillen-equivalence theorem
  6.2.5(2)–(3) for the chosen derived functors.
- `DerivedAbsoluteness.lean`: arbitrary postcomposition preserves derived
  functors computed using a left/right derivability structure.
- `QuillenAdjunction.lean`: the relative Quillen-pair conditions and
  Theorem 6.2.5(1), using mathlib's Maltsiniotis derived-adjunction argument.
- `FibrantSubcategory.lean`: native fibrant subcategory, restricted F1–F4,
  and inclusion as a general fibrant approximation.
- `RightDerivedFunctor.lean`: 6.2.1(2), the arbitrary derived-unit property
  at fibrant objects, and the full structural derived equivalence 6.2.3(2).
- `FibrantApproximation.lean`: approximation by opposites, localization
  equivalence, right derivability structure, and right-derived existence
  with invertible unit on approximation image objects.
- `FibrationBasic.lean`: prefibration categories via opposites, the
  fibrant/cofibrant object bridge, native F1–F4 consequences and fibrant
  replacements, using the existing proofs on the opposite category.
- `CofibrantSubcategory.lean`: CF1–CF4 on the full subcategory of cofibrant
  objects and the general approximation instance for its inclusion.
- `DerivedApproximationEquivalence.lean`: Theorem 6.2.3(1) under its structural
  approximation hypothesis; existence and equivalence of any derived functor.
- `CofibrantApproximationDerived.lean`: Theorem 6.2.2(1), pointwise
  derived-functor existence, and invertibility of any derived counit on
  the image of a general approximation.
- `CofibrantApproximationLocalization.lean`: the inverse localization
  functor, both comparison isomorphisms, the general localization equivalence
  (Theorem 6.1.7(1)), and the general left derivability structure.
- `CofibrantApproximationFractions.lean`: fractions between prescribed
  resolutions, independence, computation on actual source maps, pushout
  composition, and a resolution functor inverting ambient weak equivalences.
- `CofibrantApproximationHomotopy.lean`: general homotopy cancellation,
  Lemma 6.1.3(1), producing a left-homotopy witness in the source, and
  fraction independence, Lemma 6.1.4(1), under every functor inverting
  source weak equivalences.
- `DerivedEquivalence.lean`: Brown's lemma packages cofibrant restriction as
  a localizer morphism; total left derived equivalence is equivalent to that
  restriction being a localized equivalence; existence under that condition.
- `DerivedFunctorComparison.lean`: comparison with the localized cofibrant
  restriction, necessary and sufficient equivalence criterion, derived
  equivalence existence under that criterion, and comparison with the
  replacement construction. The structural approximation hypothesis of
  Theorem 6.2.3(1) is not yet formalized.
- `DerivedFunctor.lean`: cofibrant inclusion is a left derivability structure;
  existence of pointwise left derived functors and invertibility of the counit
  on cofibrant objects; Theorem 6.2.1(1) after target localization; computation
  on arbitrary cofibrant replacements and natural, coherent comparisons.
- `AmbientHomotopyFractions.lean`: ambient representations and equality criteria
  of Theorems 6.4.4(1) and 6.4.5(1), for arbitrary weak-equivalence denominators
  and the sharper trivial-cofibration case.
- `ReplacementComparison.lean`: both inverse comparison isomorphisms prove
  Theorem 6.1.6. Any ambient localization restricts to a localization of
  cofibrant objects, giving ambient equality iff left homotopy.
- `ReplacementFunctor.lean`: fractions representing ambient arrows between
  prescribed replacements, independence, identity and pushout composition,
  extension to an ambient functor, inversion of weak equivalences, and descent
  to a reverse functor on localizations; its restriction to cofibrant objects
  is naturally isomorphic to the original functor.
- `BrownFunctor.lean`: Brown's functor lemma; inverting trivial cofibrations
  between cofibrant objects suffices to invert their weak equivalences.
- `HomotopyWeakEquivalences.lean`: identities, composition, and two out of three
  for weak equivalences of the homotopy quotient.
- `TrivialCofibrationLocalization.lean`: equivalence of localization at trivial
  cofibrations and at weak equivalences, with compatible canonical functors.
- `HomotopyLocalization.lean`: functors inverting weak equivalences identify
  left-homotopic maps; the homotopy quotient maps to localization and this
  comparison is itself a localization at the quotient's weak equivalences.
  The comparison is now proved faithful, using Ore and cancellation.
  `map_eq_iff_cofibrant_leftHomotopy` detects equality for any localization
  of `CofibrantObject C`.
- `TrivialCofibrationFractions.lean`: fraction existence, pushout composition,
  common denominators, and finite families over one denominator. Numerators
  can be chosen to be cofibrations, and for a single arrow the combined
  endpoint coproduct map can also be a cofibration.
- `HomotopyFractions.lean`: sufficient equality criteria using common extensions
  with left-homotopic numerators and denominators, and exact equality criteria
  for trivial-cofibration fractions in a localization of cofibrant objects.
  Both a fixed common denominator and an existential common-extension
  formulation are available.
- `HomotopyCancellation.lean`: precomposition and postcomposition by a weak
  equivalence preserve and reflect left homotopy. Consequently every weak
  equivalence in `LeftHomotopyCategory C` is a monomorphism. The precomposition
  argument uses `weakEquivalence_coprod_map_of_weakEquivalence` in
  `Factorization.lean`: binary coproducts preserve weak equivalences between
  cofibrant objects.

Theorem 6.1.6 identifies localization of `CofibrantObject C` with localization
of the entire ambient category. Explicit ambient formulations of the fraction
theorems are now in `AmbientHomotopyFractions.lean`, with correspondence
recorded in the mathematical note.

The following is a provisional route, checked against §§6.3–6.4, rather than
a required reproduction of the paper's proof order. Prefer a shorter direct
argument or existing mathlib API whenever it establishes the same statement
under the intended hypotheses. Reassess the remaining dependencies after each
substantial result.

1. Cancellation (Theorem 6.4.3(1)(b)) is complete in both directions:
   `LeftHomotopyRel.of_postcomp_weakEquivalence`,
   `LeftHomotopyRel.of_precomp_weakEquivalence`, and the corresponding
   `iff` statements. The quotient's monomorphism instances remain available
   for the localization faithfulness argument.
2. The homotopy Ore condition (Theorem 6.4.3(1)(a)) is complete as
   `exists_strict_homotopy_ore` in `HomotopyOre.lean`. The proof follows the
   paper's cylinder construction: the pushout of the full cylinder boundary
   proves that the remaining endpoint composite is a cofibration; excision
   then proves the second pushout map is a weak equivalence. It does not
   assume that the map from the cylinder into the first pushout is a
   cofibration. `weakEquivalences_leftHomotopyCategory_hasLeftCalculusOfFractions`
   combines this square with precomposition cancellation to install mathlib's
   left calculus of fractions on the homotopy quotient.
3. The converse equality criterion is complete as
   `map_eq_iff_cofibrant_leftHomotopy`, together with the faithful comparison
   instance. This proves the cofibrant-subcategory version of
   Theorem 6.4.4(1)(c). The fixed and existential common-denominator criteria
   `trivialCofibration_fraction_map_eq_iff_leftHomotopy` and
   `trivialCofibration_fraction_map_eq_iff_exists_leftHomotopy` also give the
   cofibrant-subcategory version of Theorem 6.4.5(1)(b).
4. The ambient comparison (Theorem 6.1.6) is now constructed in
   `CofibrantReplacement.lean` and proved essentially surjective. Prescribed
   source replacements extend across arrows, and pairs of replacements have
   common extensions by trivial cofibrations. The categories of replacements
   are connected, all their morphisms are weak equivalences, and the inclusion
   on arrow categories has left resolutions. Lemma 6.1.3(1), for inclusion of
   cofibrant objects, now cancels equality after a weak equivalence to an
   arbitrary ambient object; parallel replacement comparison maps therefore
   have equal images under weak-equivalence-inverting functors.
   `AmbientFractions.lean` proves Lemma 6.1.4(1) for inclusion of cofibrant
   objects: two fractions with the same ambient numerator and denominator
   have equal images, including arbitrary weak-equivalence denominators. See
   [the mathematical note](cofibrant-replacements.md).
   `ReplacementComparison.lean` now supplies both inverse comparison
   isomorphisms, proving the equivalence and ambient equality criterion.
   `AmbientHomotopyFractions.lean` completes the ambient fraction statements
   of Theorems 6.4.4(1) and 6.4.5(1), including general weak-equivalence
   denominators. The full ambient equality criterion also gives 6.3.1(1).

Do not infer faithfulness or equivalence of the homotopy quotient's comparison
merely from its localization property. The foundation audit and elementary API
review remain separate outstanding tasks.
The original unrestricted separate-comparison claims of Lemma 1.3.4(1) have
been replaced by the correction note; they must not be assumed in subsequent
proofs.

## Duality and reuse cleanup (2026-11-09)

Apply the [duality-first style rule](development-process.md#duality-first-native-interfaces)
before extending duplicated localization machinery. This is a refactoring
backlog, not a claim that the current proofs have incorrect hypotheses.
Keep the native public APIs and the existing mathematical results.

**Status (2026-11-09): items 1–3 completed.** The duplicated proofs were
removed and their callers migrated; see the completion record after the list.

1. **Share quotient/localization machinery.** Audit mathlib's existing
   `HomRel.FactorsThroughLocalization` and quotient-localizer interfaces
   before extracting any helper. Replace the parallel constructions in
   `HomotopyLocalization.lean` and `RightHomotopyLocalization.lean`, especially
   `leftHomotopyComparisonStrictUniversalProperty` and
   `rightHomotopyComparisonStrictUniversalProperty`, by applications of one
   general result about a congruence and a morphism property. Retain the
   factorization equations and canonical comparisons used by callers.
2. **Transport the homotopy-inversion lemma.** Establish a reusable equivalence
   between `(FibrantObject C)ᵒᵖ` and `CofibrantObject Cᵒᵖ`, recording the
   underlying-arrow equations and weak-equivalence correspondence. Use this
   and `rightHomotopy_iff_op` to make `map_eq_of_fibrant_rightHomotopy` a
   wrapper around `map_eq_of_cofibrant_leftHomotopy`. The current proof
   independently repeats the path/cylinder cancellation argument. Avoid
   defining the foundational bridge in a module that already depends on
   these localization proofs.
3. **Share change-of-inverted-class machinery.** The universal-property
   constructions in `TrivialCofibrationLocalization.lean` and the current
   `TrivialFibrationLocalization.lean` should reuse a general result for
   two morphism classes with the same inverting functors. Keep Brown's
   fibration lemma as an opposite application of the cofibration lemma;
   keep the native membership lemmas and compatibility isomorphisms.

Completion record:

1. `LocalizationTransfer.lean` proves
   `Localization.quotientLift_inverts`,
   `Localization.strictUniversalPropertyFixedTargetQuotientLift`, and
   `Localization.isLocalization_quotientLift` for an arbitrary relation and
   compatible morphism classes. Mathlib's `HomRel.FactorsThroughLocalization`
   was inspected first: it proves the converse direction (quotient functor
   followed by a localization of the quotient) and is still used for the
   localized equivalences; it does not supply the strict universal property
   of the lift of `W.Q`. Both `leftHomotopyComparisonStrictUniversalProperty`
   and `rightHomotopyComparisonStrictUniversalProperty`, the `_inverts`
   theorems, and the `_isLocalization` instances are now one-line
   applications; their hand-written proofs were deleted. Names and
   statements are unchanged.
2. `FibrantOpposite.lean` (imports only `FibrationBasic.lean` and mathlib)
   constructs `fibrantObjectOpEquivalence : (FibrantObject C)ᵒᵖ ≌
   CofibrantObject Cᵒᵖ` with `rfl` object/arrow equations,
   `weakEquivalence_fibrantObjectOpEquivalence_functor_map_iff`,
   `weakEquivalence_fibrantObjectOpEquivalence_inverse_map_iff`,
   `weakEquivalences_cofibrantObject_op_inverseImage`, and
   `isInvertedBy_inverse_comp_op_iff`.
   `map_eq_of_fibrant_rightHomotopy` is now `map_eq_of_cofibrant_leftHomotopy`
   applied to `fibrantObjectOpEquivalence.inverse ⋙ F.op`, with
   `rightHomotopy_iff_op` translating the hypothesis; the native path-object
   cancellation proof was deleted.
3. `Localization.strictUniversalPropertyFixedTargetQOfIsInvertedBy` and
   `Localization.isLocalization_of_isInvertedBy_Q` (no mathlib equivalent
   was found) replace both hand-written universal-property proofs. Each side
   now supplies only its two inversion facts
   (`cofibrantTrivialCofibrations_isInvertedBy_weakEquivalences_Q`,
   `weakEquivalences_isInvertedBy_cofibrantTrivialCofibrations_Q`, and the
   fibrant analogues) from Brown's lemma. `trivial(Co)fibrationLocalizationUniversalProperty`,
   the `_isLocalization` instances,
   `isLocalization_trivial(Co)fibrations_of_weakEquivalences`, and the
   canonical comparison equivalences with their `_fac` isomorphisms keep
   their names and statements. `BrownFibration.lean` is unchanged: the
   fibrant Brown lemma is still the cofibrant lemma applied in `Cᵒᵖ`.

Public API: only additions (the declarations above); no existing statement,
name, or hypothesis changed. Full build passed (2018 jobs) without warnings;
`git diff --check` is clean; `#print axioms` for the refactored results
lists only `propext`, `Classical.choice`, and `Quot.sound`.

Remaining, deliberately not changed: the native faithfulness proof and
`map_eq_iff_fibrant_rightHomotopy` in `RightHomotopyLocalization.lean` are
short mathlib-calculus glue around transported cancellation, mirroring the
left side; transporting them through `fibrantObjectOpEquivalence` would not
shorten them materially. The chosen-object adapters listed below remain.

Do not rewrite all native proofs indiscriminately. The chosen-object
comparisons in `FibrationBasic.lean` and `HomotopyOpposite.lean` are necessary
transport infrastructure. The small native terminal/pullback constructions
in `FibrantSubcategory.lean` and diagonal factorization in `PathObject.lean`
may remain documented adapters. Revisit them only if the new foundational
bridge makes reuse materially simpler, without creating import cycles.
Cancellation, the strict Ore construction, and the right-fraction criteria
already reuse the cofibration-side theorems and are not primary cleanup targets.

For each cleanup increment, preserve public theorem statements and comparison
equations, compile the existing callers, run the full library build, and
update the notes to reflect the changed proof organization. Do not add
mathematical assumptions to make the transport convenient.

## Parallel workstream — mathematical exposition

Maintain readable mathematical explanations alongside the Lean library. These
notes should let a mathematician review the definitions, statements, and proof
constructions without reading tactic scripts. They complement module docstrings
and declaration documentation in the Lean files.

### Documents to produce

Use `docs/mathematics/` for the exposition. Organize it by mathematical subject;
a substantial Lean module usually merits a matching note, while small supporting
modules can share one. The initial documentation backlog is:

| Status | Document | Lean coverage |
| --- | --- | --- |
| Planned | `index.md` | Reading order, dependency diagram, and coverage map |
| Planned | `foundations.md` | `Basic.lean`: CF1–CF6, supplied structures, cofibrancy, and size conventions |
| Planned | `coproducts.md` | `Coproducts.lean`: binary and finite constructions, including the empty case |
| Planned | `factorization.md` | `Factorization.lean`: Brown, relative, and compatible factorizations |
| Planned | `gluing-and-excision.md` | `Gluing.lean` and `Extension.lean`: the repaired gluing argument and excision |
| Planned | `cylinders.md` | `Cylinder.lean`: existence, relative cylinders, refinement, reversal, and concatenation |
| Planned | `left-homotopy.md` | `LeftHomotopy.lean`: strict versus enlarged-target homotopy and composition |
| Planned | `homotopy-quotient-and-localization.md` | `HomotopyCategory.lean` and `HomotopyLocalization.lean`: quotient, weak equivalences, comparison, and precise limits of proved results |

### Required content and review

Each note should include:

1. Its purpose, prerequisites, and references to the fixed version of the paper.
2. Precise mathematical definitions and theorem statements, retaining all
   substantive hypotheses.
3. LaTeX equations, commutative diagrams, and explanations of the proof's main
   constructions. Add element-level diagrams when they clarify an example.
4. Examples or counterexamples where useful.
5. A correspondence table linking the paper's notation and theorem numbers to
   actual Lean declarations and source files.
6. A clear account of what is formalized, what is only explained informally,
   and what remains unproved.

Use the paper's notation in mathematical exposition, with an explicit key for
different Lean names. Explain mathematical choices rather than individual tactics.
In particular, distinguish strict left homotopy from the paper's left homotopy,
and distinguish the homotopy quotient from its localization. Link to the existing
[relative Brown correction](relative-brown-factorization.md) rather than creating
a competing account of that correction.

Review statements against the actual Lean signatures and their dependencies,
not just declaration names or the roadmap. Check rendered equations and diagrams
in Markdown preview, verify source links, and check the reading order. A successful
Lean build does not certify the accuracy of explanatory prose. Record the code
revision reviewed and any relevant uncommitted changes when handing off a draft.

### Background-agent handoff

This workstream is suitable for a separate documentation agent running alongside
proof development, delegated from the main conversation. Give that agent one or
a few related notes at a time, beginning with foundations and coproducts.

The documentation agent should read the corresponding Lean modules and paper
sections, draft only its assigned files under `docs/mathematics/`, and report
mathematical or source-correspondence questions for review. It should not edit
Lean proofs, shared roadmap files, or Git state as part of this assignment.
Keep file ownership separate from the agent implementing proofs. The main agent
reviews the drafts, reconciles them with ongoing code changes, and updates this
backlog after acceptance. Agent execution must be initiated in the main
conversation; this side conversation has not started a background agent.

For subsequent increments, update the corresponding mathematical note whenever
a public statement, hypothesis, construction, or formalization status changes.
Treat that documentation update as part of completing the increment.

## Progress log

| Date | Increment | Status / evidence |
| --- | --- | --- |
| 2026-11-07 | Inspect existing modules and create this roadmap | Plan created; foundation audit and build pending |
| 2026-11-07 | Baseline validation | `lake build` passed (1808 jobs) |
| 2026-11-07 | Binary coproduct foundation | Six declarations in `Coproducts.lean`; exported by the library root; `lake build` passed (1810 jobs), without warnings |
| 2026-11-07 | Binary maps and finite existence | Four binary-map declarations and two `Fin n` coproduct declarations; `lake build` passed (1822 jobs), without warnings |
| 2026-11-07 | Complete Lemma 1.2.1(1) | Finite-family map properties and four results for arbitrary finite indexing types; `lake build` passed (1822 jobs), without warnings |
| 2026-11-07 | Brown factorization | Lemma 1.3.1(1) and Remark 1.3.2 in `Factorization.lean`, exported by the library root; `lake build` passed (1824 jobs), without warnings |
| 2026-11-07 | Relative factorization | Lemma 1.3.3(1), with the pushout comparison cofibration and all square equations; `lake build` passed (1824 jobs), without warnings |
| 2026-11-07 | Compatible Brown factorization and obstruction | Weaker combined-comparison theorem plus a checked injectivity obstruction to the separate target-side claim; full Lemma 1.3.4(1) unresolved; `lake build` passed (1826 jobs), without warnings |
| 2026-11-07 | Cylinder existence and endpoint properties | Definition 1.5.1(1) represented by mathlib's good cylinders; Lemma 1.5.2(1) and five elementary properties in `Cylinder.lean`; `lake build` passed (1832 jobs), without warnings |
| 2026-11-07 | Gluing lemma | Both parts of Lemma 1.4.1(1) in `Gluing.lean`, using restricted Brown comparisons along cofibration edges and compatible Brown replacement elsewhere; `lake build` passed (1834 jobs), without warnings |
| 2026-11-07 | Excision and relative cylinders | Lemma 1.4.2(1) in `Extension.lean` and Lemma 1.5.3(1) in `Cylinder.lean`; `lake build` passed (1836 jobs), without warnings |
| 2026-11-07 | Cylinder operations | Goodness under endpoint reversal and concatenation in `Cylinder.lean`, using CF1–CF4; `lake build` passed (1836 jobs), without warnings |
| 2026-11-07 | Left homotopy | Common cylinder refinements, strict and enlarged-target relations, Lemma 6.3.2(1), and Theorem 6.3.3(1); `lake build` passed (1864 jobs), without warnings |
| 2026-11-07 | Homotopy quotient category | Congruence on cofibrant objects, exact quotient equality criterion, and descent of weak equivalences in `HomotopyCategory.lean`; `lake build` passed (1870 jobs), without warnings |
| 2026-11-07 | Localization comparison and Brown functor lemma | Comparison functors and their universal properties; equivalence of localization at weak equivalences and at trivial cofibrations on cofibrant objects |
| 2026-11-07 | Fraction representations and operations | Cofibrant-subcategory fraction existence, composition, common denominators, finite families, cofibration numerators, and sufficient homotopy equality criteria; `lake build ABCCofibrations` passed (1888 jobs), without warnings |
| 2026-11-07 | Postcomposition cancellation | `HomotopyCancellation.lean` proves reflection of left homotopy by weak equivalences and monomorphism instances in the homotopy quotient; `lake build ABCCofibrations` passed (1890 jobs), without warnings |
| 2026-11-07 | Precomposition cancellation | Theorem 6.4.3(1)(b)(i) and preservation of weak equivalences by binary coproducts of cofibrant objects; `lake build ABCCofibrations` passed (1890 jobs), without warnings |
| 2026-11-08 | Homotopy Ore condition | Theorem 6.4.3(1)(a), the full-boundary pushout cofibration argument, and left calculus of fractions on the homotopy quotient; `lake build ABCCofibrations` passed (1892 jobs), without warnings |
| 2026-11-08 | Localization equality criteria | Faithful comparison, equality iff left homotopy for localization of cofibrant objects, and exact trivial-cofibration fraction comparison criteria; `lake build ABCCofibrations` passed (1892 jobs), without warnings |
| 2026-11-08 | Ambient comparison: objects and replacements | Constructed the ambient localization comparison and proved essential surjectivity; extensions across arrows and common extensions of replacements in `CofibrantReplacement.lean`; `lake build ABCCofibrations` passed (1898 jobs), without warnings. Full faithfulness remains open. |
| 2026-11-08 | Compatibility of replacements | Replacement categories are connected, all their morphisms are weak equivalences, and every ambient arrow has a cofibrant replacement square; `lake build ABCCofibrations` passed (1898 jobs), without warnings. |
| 2026-11-08 | Ambient cancellation | Lemma 6.1.3(1) for inclusion of cofibrant objects, strict-homotopy reflection with arbitrary ambient codomain, and equality of parallel replacement maps under weak-equivalence-inverting functors; `lake build ABCCofibrations` passed (1898 jobs), without warnings. |
| 2026-11-08 | Independence of ambient fraction choices | Lemma 6.1.4(1) for inclusion of cofibrant objects in `AmbientFractions.lean`, with arbitrary weak-equivalence denominators and a separate pushout proof for trivial-cofibration denominators; `lake build ABCCofibrations` passed (1900 jobs), without warnings. |
| 2026-11-08 | Replacement functor and reverse localization functor | `ReplacementFunctor.lean` constructs fractions between prescribed replacements, proves independence and functor laws, inverts ambient weak equivalences, and descends to `ambientLocalizationToCofibrant`; comparison isomorphisms remain open. `lake build ABCCofibrations` passed (1902 jobs), without warnings. |
| 2026-11-08 | Left-inverse comparison and ambient faithfulness | `replacementFunctorRestrictionIso`, `cofibrantLocalizationReplacementIso`, and `cofibrantLocalizationToAmbient_faithful`; the other inverse comparison and fullness remain open. Documentation now explicitly records differences from the paper. `lake build ABCCofibrations` passed (1904 jobs), without warnings. |
| 2026-11-08 | Ambient localization equivalence | Both inverse comparisons prove Theorem 6.1.6; restriction of any ambient localization is a localization of cofibrant objects, and `ambient_map_eq_iff_cofibrant_leftHomotopy` proves Theorem 6.4.4(1)(c). `lake build ABCCofibrations` passed (1904 jobs), without warnings. |
| 2026-11-08 | Ambient homotopy fractions | The cofibration-side statements of 6.4.4 and 6.4.5: strong fraction representations and both general and trivial-cofibration denominator equality criteria. `HomotopyFractions.lean` supplies the general converse via the quotient calculus. `lake build ABCCofibrations` passed (1906 jobs), without warnings. |
| 2026-11-08 | Total left derived functors | `DerivedFunctor.lean` uses the left derivability structure of cofibrant inclusion to prove Theorem 6.2.1(1), with pointwise existence and counit invertible on cofibrant objects. `lake build ABCCofibrations` passed (1942 jobs), without warnings. |
| 2026-11-08 | Derived-functor computation on replacements | Computation isomorphism for any cofibrant replacement, counit equations, naturality for replacement squares, and coherent comparisons between computed values; `lake build ABCCofibrations` passed (1942 jobs), without warnings. |
| 2026-11-08 | Derived comparison and equivalence criterion | `DerivedFunctorComparison.lean` compares arbitrary left derived functors with the lifted cofibrant restriction and the replacement construction, and proves the derived-equivalence criterion. Full structural 6.2.3(1) remains open. `lake build ABCCofibrations` passed (1944 jobs), without warnings. |
| 2026-11-08 | Localizer criterion for total derived equivalences | `DerivedEquivalence.lean` constructs the restriction localizer via Brown's lemma, proves the iff criterion for arbitrary localizations, and derives existence. Structural CFA1–CFA4 remain next. `lake build ABCCofibrations` passed (1946 jobs), without warnings. |
| 2026-11-08 | General cofibrant approximation axioms and resolutions | Definition 6.1.1, identity example, image cofibrancy, induced localizer, object and arrow resolutions, common extensions, and connectedness; general localized equivalence remains open. `lake build ABCCofibrations` passed (1948 jobs), without warnings. |
| 2026-11-08 | General approximation homotopy cancellation | `CofibrantApproximationHomotopy.lean` proves Lemma 6.1.3(1) with an explicit left-homotopy witness, following the paper and preserving the restriction on CFA3. Full build passed (1950 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: Lemma 6.1.4(1), independence of fraction choices. |
| 2026-11-08 | General approximation fraction independence | Lemma 6.1.4(1) is proved under every functor inverting source weak equivalences, using common resolutions and homotopy cancellation. The note explains the difference from the paper. Full build passed (1950 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: fractions between prescribed general resolutions and the inverse functor. |
| 2026-11-08 | Fractions and the general resolution functor | Fractions between prescribed resolutions retain two cofibration legs; existence, independence, computation on actual source arrows, and pushout composition are proved. `resolutionFunctor` respects identities and composition and inverts ambient weak equivalences. Full build passed (1952 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: localization lift and inverse comparison isomorphisms. |
| 2026-11-08 | General cofibrant approximation localization equivalence | `CofibrantApproximationLocalization.lean` constructs the inverse and both natural comparison isomorphisms, proves Theorem 6.1.7(1), and then obtains the general left derivability structure. Corrected v4 lemma citations: cancellation is 6.1.3(1), fraction independence is 6.1.4(1). Full build passed (1954 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: the full structural hypotheses of 6.2.2(1) and 6.2.3(1). |
| 2026-11-08 | Derived functors from general approximations | `CofibrantApproximationDerived.lean` proves Theorem 6.2.2(1) under its full hypothesis on the composite, pointwise existence, and invertibility of any derived counit on approximation image objects. No target two-out-of-three or saturation axiom is added. Full build passed (1956 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: cofibrant-subcategory structure and the structural version of 6.2.3(1). |
| 2026-11-08 | Cofibrant subcategory and structural derived equivalence | CF1–CF4 restrict to `CofibrantObject C`, and its inclusion is a general cofibrant approximation. `DerivedApproximationEquivalence.lean` proves Theorem 6.2.3(1), with existence and equivalence of any total left derived functor. Full build passed (1960 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: opposite-category/right-derived infrastructure and audit the shorter Maltsiniotis route before Quillen adjunction. |
| 2026-11-08 | Prefibration foundation by duality | `FibrationBasic.lean` defines F1–F4 through the opposite precofibration category and proves the fibrant/cofibrant bridge plus native F1–F4 consequences and fibrant replacements. The new note explains differences from the paper and records mathlib's Maltsiniotis derived-adjunction interface. Full build passed (1962 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: fibrant approximations and right-derived existence. |
| 2026-11-08 | Fibrant approximations and total right-derived existence | `FibrantApproximation.lean` dualizes the approximation class, transports localization equivalence and right derivability, and proves 6.2.2(2) under the weaker composite preservation hypothesis with invertibility of any derived unit on image objects. The note records differences from v4. Full build passed (1970 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: fibrant-subcategory instances and 6.2.1(2)/6.2.3(2). |
| 2026-11-08 | Native fibrant subcategory and right-derived equivalences | `FibrantSubcategory.lean` supplies F1–F4 on mathlib's fibrant subcategory and its inclusion approximation. `RightDerivedFunctor.lean` proves 6.2.1(2), invertibility of any derived unit at fibrant objects, and 6.2.3(2) under its structural approximation hypothesis. Full build passed (1976 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: postcomposition preservation for Maltsiniotis's derived adjunction argument. |
| 2026-11-08 | Absolute derived functors and Quillen adjunction | `DerivedAbsoluteness.lean` proves postcomposition preservation using mathlib's image-object criterion. `QuillenAdjunction.lean` records 6.2.4(1)–(3), proves 6.2.5(1) for arbitrary total derived functors, and proves joint existence, using Maltsiniotis's argument. The note explains the changed proof route. Full build passed (1984 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: derived comparison formulas and 6.2.5(2)–(3). |
| 2026-11-08 | Quillen comparison and equivalence criteria | `QuillenComparison.lean` exposes the derived unit/counit and adjoint-arrow equations, proves both one-sided full-faithfulness criteria of 6.2.5(2), records Definition 6.2.4(4), and constructs the derived equivalence of 6.2.5(3). The note explains the direct comparison-formula proof and unchanged hypotheses. Full build passed (1986 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: native dual homotopy/path-object interface. |
| 2026-11-08 | Native path objects and initial right-homotopy API | `PathObject.lean` proves restricted binary products, good path-object existence (1.5.2(2)), trivial-fibration projections, fibrancy, and reversal. `RightHomotopy.lean` defines the strict/general native relations and proves reflexivity, symmetry, precomposition, and weak-equivalence invariance. The note explains the use of native F3/F4 rather than silently identifying product choices with opposite coproducts. Full build passed (1994 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: explicit opposite comparison, transitivity, and 6.3.1(2). |
| 2026-11-09 | Native/opposite homotopy bridge and right fractions | `HomotopyOpposite.lean` proves the chosen-product/coproduct comparison and strict/general homotopy equivalence, transferring transitivity, postcomposition, and 6.3.1(2). `RightHomotopyCancellation.lean` transfers weak-equivalence cancellation. `RightHomotopyFractions.lean` proves 6.4.4(2)(a) with trivial-fibration denominators and common-denominator equality. Full build passed (2000 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: different-denominator equality 6.4.4(2)(b) and full-boundary refinement 6.4.5(2). |
| 2026-11-09 | Right-fraction equality and product-boundary refinement | `RightHomotopyFractions.lean` proves 6.4.4(2)(b) for arbitrary weak-equivalence denominators, 6.4.5(2)(a) with fibrant product boundary, and 6.4.5(2)(b) with trivial-fibration common refinements and exact denominator equality. Alongside the previous localization criterion, the right-side 6.4.4 and 6.4.5 statements are complete. The note explains the opposite transport and equation-based evaluation interface. Full build passed (2000 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: native right-homotopy quotient and calculus of fractions. |
| 2026-11-09 | Native right-homotopy quotient and calculus | The native quotient on `FibrantObject C` has equality exactly right homotopy and descended weak-equivalence laws. Its equivalence with the opposite left quotient preserves and reflects weak equivalences. The transported strict Ore square completes 6.4.3(2)(a), and native cancellation supplies a right calculus of fractions. Full build passed (2008 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: compare localization of the quotient with fibrant-object and ambient localizations. |
| 2026-11-09 | Right-homotopy quotient localization and ambient comparison | `RightHomotopyLocalization.lean` proves the unique quotient factorization for inverting functors, the strict localization universal property, equivalence between quotient and fibrant-object localizations, and the native fibrant inclusion equivalence 6.1.6(2). Their composite gives ambient localization. The note explains the native universal-property proof and reuse of the general approximation theorem. Full build passed (2010 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: faithfulness and the arbitrary fibrant-localization equality criterion. |
| 2026-11-09 | Faithfulness and arbitrary fibrant-localization equality | `RightHomotopyLocalization.lean` proves that weak-equivalence classes are epimorphisms, the quotient comparison is faithful, and any fibrant-object localization identifies exactly right-homotopic representatives. The note records the native dual argument and distinguishes faithfulness from fullness. Full build passed (2010 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: localization at trivial fibrations and its comparison with weak-equivalence localization. |
| 2026-11-09 | Trivial-fibration localization | `BrownFibration.lean` proves Brown's functor lemma for fibrant objects by transporting the cofibrant lemma across the opposite category. `TrivialFibrationLocalization.lean` identifies localization at trivial fibrations with localization at all weak equivalences, compatibly with the canonical functors, and proves the pullback Ore square. The note records that this is the dual of the cofibrant comparison and not a separate numbered theorem. Full build passed (2014 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: right-fraction representations with trivial-fibration denominators. |
| 2026-11-09 | Duality and reuse cleanup | `LocalizationTransfer.lean` proves the quotient-lift and same-inverting-classes localization lemmas once; the left/right homotopy-quotient comparisons and both trivial-(co)fibration comparisons are now applications, with their duplicated proofs removed. `FibrantOpposite.lean` adds `(FibrantObject C)ᵒᵖ ≌ CofibrantObject Cᵒᵖ`, and `map_eq_of_fibrant_rightHomotopy` is now a transport of `map_eq_of_cofibrant_leftHomotopy`. Public statements unchanged; notes updated. Full build passed (2018 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. |
| 2026-11-09 | Trivial-fibration right fractions | `TrivialFibrationFractions.lean` proves representation by right fractions with trivial-fibration denominators, common refinements, equality over a refinement, composition, finite common denominators, and fibration numerators with product boundary. Each result transports `TrivialCofibrationFractions.lean` through `fibrantObjectOpEquivalence`, using new general localization/fraction transport in `FibrantOpposite.lean`. Plan wording on Lemma 1.3.4(1) corrected: the original claim is refuted and the corrected statement proved. Full build passed (2020 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: foundation audit and Chapter 1 backlog. |
| 2026-11-09 | Foundation audit (Milestone 0) | `docs/axiom-correspondence.md` maps every clause of Definition 1.1.1 and F1–F4 to Lean fields or derived results; no discrepancy, no definition changed. `Basic.lean` adds independence of the chosen initial object, the empty-coproduct case from CF1, all CF6 composites from successive maps, the CF5 existence equivalence, and CF5/CF6 for arbitrary colimit representatives. Full build passed (2020 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: Chapter 1 §1.6. |
| 2026-11-09 | Sums of weak equivalences (§1.6) | `SmallSums.lean` proves Lemma 1.6.2(1) for finite (CF1–CF4) and small (CF5) families and Lemma 1.6.3(1), all from `weakEquivalence_sigmaMap_of_trivialCofibrations`. Checked that the proof of 1.6.4(1) needs only the cofibration-edge relative Brown lemma, not the refuted claims of 1.3.4(1). Full build passed (2022 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: Lemma 1.6.4(1). |
| 2026-11-09 | Colimits of CF6 sequences (§1.6) | `SequentialColimits.lean` proves Lemma 1.6.4(1) (Reedy step by pushout pasting plus inductively chosen compatible Brown factorizations) and Lemma 1.6.5(1), with CF6 stated as standalone hypotheses so only CF1–CF4 and CF6 are used. The inductive step uses `exists_relative_brown_of_cofibration_edges`, not the refuted separate claims of 1.3.4(1). Full build passed (2030 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: §1.7 over/under categories, or Lemma 1.6.1. |
| 2026-11-09 | CF5 hypotheses for Lemma 1.6.2(1) | `SmallSums.lean` adds standalone `CoproductCofibrationAxiom` and `TrivialCoproductAxiom`; the small case of 1.6.2(1) now assumes CF1–CF5 only, with the cofibration-category version kept as a wrapper of the same name. Full build passed, without warnings. |
| 2026-11-09 | Over and under categories (§1.7) | `OverUnder.lean` defines the induced classes on `Under A` (a mathlib TODO) and proves Proposition 1.7.1(1), CF1–CF4 part: `Over A` is a precofibration category, and so is `Under A` for cofibrant `A`. Pushouts are created by the forgetful functors. Full build passed (2214 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: §1.8 properness, then the CF5–CF6 and dual parts of 1.7.1. |
| 2026-11-10 | `to_dual` for the `Under` classes | `OverUnder.lean` now generates `underCategoryWithCofibrations` and `underCategoryWithWeakEquivalences` from mathlib's `Over` instances with `to_dual`, using temporary local registrations in `ToDualRegistrations.lean`; names, types, and instance status unchanged. The project's duality method otherwise remains transport through opposites. Full build passed (2216 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. |
| 2026-11-10 | Properness, first part (§1.8) | `Properness.lean` defines PCF and left proper maps (for every pushout square), proves left properness when all objects are cofibrant (excision), and Theorem 1.8.4(1)(a). Full build passed (2218 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: Theorem 1.8.4(1)(b)–(d). |
| 2026-11-10 | Properness, Theorem 1.8.4(1)(b)–(d) | `Properness.lean` proves stability of left proper maps under pushout and composition and for isomorphisms, the left proper factorization (b), pushout stability of trivial left proper maps (c), the precofibration structure on `LeftProperCofibrations C` (d), and Proposition 1.8.5(1). Full build passed (2218 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. |
| 2026-11-10 | Properness, completion of §1.8 | `Properness.lean` adds Propositions 1.8.6(1) and 1.8.7(1), with the paper's cocompleteness replaced by the existence of the pushouts used. `RightProperness.lean` defines PF and right proper maps through the opposite category, with pullback formulations, and proves Theorem 1.8.4(2)(a)–(d) and Propositions 1.8.5(2)–1.8.7(2) by duality. Full build passed (2220 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: the fibration statement of Proposition 1.7.1 and the remaining §1.6–1.7 items. |
| 2026-11-10 | Over and under categories, statement (2) | `EquivalenceTransfer.lean` transports a precofibration structure along an equivalence identifying cofibrations and weak equivalences. `OverUnder.lean` generates the induced fibrations on `Under A` by `to_dual`. `OverUnderFibration.lean` proves Proposition 1.7.1(2), F1–F4 part, via mathlib's `Over.opEquivOpUnder` and `Under.opEquivOpOver` (the class identifications hold by `rfl`). Full build passed (2224 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. Next: CF5–CF6 for over and under categories, and the remaining §1.6 items. |
| 2026-11-10 | Over and under categories, CF5–CF6 | `OverUnderCofibrationCategory.lean` transfers CF5–CF6 along forgetful functors that create the relevant colimits, constructs coproducts in `Under A` as pushouts, and proves Proposition 1.7.1(1) for cofibration categories. `FibrationCategory.lean` defines `ABCFibrationCategory`; with transport along equivalences, `OverUnderFibration.lean` proves 1.7.1(2) for fibration categories. `SmallSums.lean` now exposes its definitions. Full build passed (2228 jobs), without warnings; axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`. |

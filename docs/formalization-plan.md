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

These are existing implementations, not yet a completed audit of correspondence
with the paper. This documentation change does not establish a fresh build result.

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

- [ ] Compare every field of the existing classes with Definition 1.1.1.
  Record a field-to-axiom correspondence, including which clauses are derived.
- [ ] Check cofibrancy hypotheses, the scope of CF5, and the sequential diagrams
  used for CF6. Check empty families and universe restrictions explicitly.
- [ ] Review interaction with mathlib's morphism-property instances; avoid
  overlapping instances and unnecessary global choices.
- [ ] Build the existing library and record the baseline result.

Deliverable: a trustworthy foundation and a short correspondence note in `docs/`.
Change the current definitions only when this review identifies a concrete issue.

## Milestone 1 — Elementary API and finite coproducts

- [ ] Add convenient lemmas for identities, composition, isomorphisms, and
  two-out-of-three where existing mathlib interfaces do not already suffice.
- [ ] Expose pushout constructions and their cofibration/trivial-cofibration
  properties without requiring callers to invoke class fields repeatedly.
- [ ] Develop finite coproducts of cofibrant objects from CF1–CF4, using the
  relevant results in §1.2 rather than assuming CF5.
- [ ] Prove the corresponding elementary properties of coproduct inclusions
  and maps, with the paper's hypotheses checked individually.

Suggested module: `ABCCofibrations/Coproducts.lean`. Keep genuinely foundational
lemmas in `Basic.lean`; avoid splitting files until there is a coherent API.

## Milestone 2 — Factorization and extension lemmas

- [ ] Translate the cofibration-side statements of §1.3 into a dependency list.
- [ ] Formalize the factorization lemmas in that order.
- [ ] Do the same for the extension lemmas of §1.4.
- [ ] Extract reusable commutative-square and pushout lemmas when multiple proofs
  need them, reusing mathlib's universal-property interfaces.

Suggested modules: `Factorization.lean` and `Extension.lean`.
Keep existential factorizations as the default; introduce chosen data locally
when a construction needs it, without assuming functoriality.

## Milestone 3 — Cylinders and elementary homotopy

- [ ] Define cylinder objects in a form compatible with §1.5 and mathlib's
  existing abstractions, after comparing the available interfaces.
- [ ] Construct cylinders for cofibrant objects using the preceding milestones.
- [ ] Introduce left homotopy and prove only the elementary properties justified
  by the available hypotheses.
- [ ] Identify and defer claims that need the later homotopy-category theory.

Suggested module: `Cylinder.lean`. First deliverable: the cylinder existence
theorem, with its source statement and prerequisites documented.

## Milestone 4 — Complete the selected Chapter 1 foundations

- [ ] Develop the consequences of CF5 and CF6 in §1.6, including useful APIs for
  coproducts and sequential composites.
- [ ] Treat over and under categories (§1.7), making object restrictions explicit.
- [ ] Formalize the properness results (§1.8) needed by subsequent work.
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

Start with Milestone 0: audit Definition 1.1.1 and run the baseline build.
Then select the smallest missing finite-coproduct result from §1.2. Record its
exact paper number and Lean declaration here before moving to the next result.

## Progress log

| Date | Increment | Status / evidence |
| --- | --- | --- |
| 2026-11-07 | Inspect existing modules and create this roadmap | Plan created; foundation audit and build pending |

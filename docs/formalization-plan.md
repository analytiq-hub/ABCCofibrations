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

The baseline `lake build` passed on 2026-11-07. The definitions still need a
completed audit of correspondence with the paper.

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
- [ ] Create `docs/axiom-correspondence.md`, mapping every field to Definition
  1.1.1 and explaining the separately supplied category structures and initial
  object. For clauses represented by derived results, cite those declarations.
- [ ] Check that the converse presentation of CF5 follows using identities,
  and document how target cofibrancy is derived from composition.
- [ ] Check universe behavior on empty, finite, and countable indexing types.
  Distinguish the natural-number diagram category from the coproduct universe.
- [ ] Review transport to another chosen initial object and to isomorphic
  representatives of the colimits used in the axioms.

Interface decision already established by inspection: mathlib's coproduct
inclusion instances in `ModelCategory/IsCofibrant.lean` require unrestricted
`IsStableUnderCobaseChange`. Our CF3 has cofibrancy hypotheses, so use its
restricted square lemmas directly. Do not install the stronger instance.
Likewise, do not assert unrestricted `ContainsIdentities` or `RespectsIso` for
cofibrations without a separate justification covering noncofibrant sources.

Completion criterion: every axiom clause has a recorded correspondence, with
any discrepancy fixed and checked by a build. Until then the audit remains open.

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
comparison. This is a weaker replacement; the full lemma remains unresolved.
The strengthened original statement must be corrected or clarified before
using its separate-comparison claims in §1.4.

### F. Extension and cylinder entry point

Before starting §1.4, make a statement-by-statement dependency list and select
its first cofibration-side lemma. Keep that work separate from the basic Brown
factorization increment. In particular, audit the uses of Lemma 1.3.4 in the
gluing argument against the obstruction recorded in package E.

For §1.5, inspect the existing `HomotopicalAlgebra.Precylinder`, `Cylinder`, and
`Cylinder.IsGood` interfaces in mathlib's `ModelCategory/Cylinder.lean` before
defining a project-specific structure. These interfaces already exist; their
existence theorems may require stronger assumptions. First attempt to construct
a good cylinder using our factorization field and package B. Prove the endpoint
properties under the ABC assumptions. Defer the broader homotopy relation API
until its required extension results have been established.

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

Resolve the intended separate-comparison statement of Lemma 1.3.4(1) before
relying on it for the gluing argument. Independent work can continue with the
foundation correspondence audit and cylinder existence. The finite-coproduct
portion of Milestone 1, basic Brown factorization, relative factorization, and
the weaker compatible Brown construction are complete. The full Lemma 1.3.4(1)
and the elementary API review remain open.

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

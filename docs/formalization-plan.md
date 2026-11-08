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

The identification of left homotopy with equality in the localization
(Theorem 6.3.1(1)) is deferred until the necessary localization and calculus
of fractions results are available.

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

The comparison functor is implemented. Current proof development is in the
localization project (Chapters 5–7), beyond the completed elementary homotopy
work of Milestone 3. Milestones 0, 1, 2, and 4 retain their unchecked items.

Completed localization infrastructure:

- `BrownFunctor.lean`: Brown's functor lemma; inverting trivial cofibrations
  between cofibrant objects suffices to invert their weak equivalences.
- `HomotopyWeakEquivalences.lean`: identities, composition, and two out of three
  for weak equivalences of the homotopy quotient.
- `TrivialCofibrationLocalization.lean`: equivalence of localization at trivial
  cofibrations and at weak equivalences, with compatible canonical functors.
- `HomotopyLocalization.lean`: functors inverting weak equivalences identify
  left-homotopic maps; the homotopy quotient maps to localization and this
  comparison is itself a localization at the quotient's weak equivalences.
- `TrivialCofibrationFractions.lean`: fraction existence, pushout composition,
  common denominators, and finite families over one denominator. Numerators
  can be chosen to be cofibrations, and for a single arrow the combined
  endpoint coproduct map can also be a cofibration.
- `HomotopyFractions.lean`: sufficient equality criteria using common extensions
  with left-homotopic numerators and denominators.
- `HomotopyCancellation.lean`: precomposition and postcomposition by a weak
  equivalence preserve and reflect left homotopy. Consequently every weak
  equivalence in `LeftHomotopyCategory C` is a monomorphism. The precomposition
  argument uses `weakEquivalence_coprod_map_of_weakEquivalence` in
  `Factorization.lean`: binary coproducts preserve weak equivalences between
  cofibrant objects.

These results concern localization of `CofibrantObject C`. They do not yet
identify it with localization of the entire ambient category (Theorem 6.1.6).
In particular, the existence results establish the cofibrant-subcategory versions
of Theorems 6.4.4(1)(a) and 6.4.5(1)(a), not their full ambient statements.

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
2. Prove the homotopy Ore condition (Theorem 6.4.3(1)(a)), and install the
   left calculus of fractions on the homotopy quotient using mathlib.
3. Deduce the converse equality criterion for localization of cofibrant objects:
   equal localized maps are left homotopic. This completes the corresponding
   subcategory version of Theorem 6.4.4(1)(c).
4. Prove the ambient comparison (Theorem 6.1.6) to obtain the full
   Theorem 6.3.1(1), and finish the converse fraction equality criteria of
   Theorems 6.4.4(1)(b) and 6.4.5(1)(b).

Do not infer faithfulness or equivalence of the homotopy quotient's comparison
merely from its localization property. The foundation audit and elementary API
review remain separate outstanding tasks.
The original unrestricted separate-comparison claims of Lemma 1.3.4(1) have
been replaced by the correction note; they must not be assumed in subsequent
proofs.

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

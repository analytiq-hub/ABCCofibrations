# ABCCofibrations

Anderson–Brown–Cisinski cofibration categories, following Definition 1.1.1 of
Rădulescu-Banu, [*Cofibrations in Homotopy Theory*](https://arxiv.org/abs/math/0610009).

This is a standalone Lean project. Build it with `lake build`.

Import `ABCCofibrations.Basic` for:

- `ABCCofibrations.ABCPrecofibrationCategory C`: CF1–CF4.
- `ABCCofibrations.ABCCofibrationCategory.{w} C`: CF1–CF6, with coproducts indexed
  by `Type w`.

Import `ABCCofibrations.Coproducts` for finite coproducts of cofibrant objects
and preservation of (trivial) cofibrations by finite coproduct maps
(Lemma 1.2.1(1)). The results support any finite indexing type in any universe,
including the empty family, and require only CF1–CF4. Binary coproduct inclusion
and map lemmas are also provided.

Import `ABCCofibrations.Factorization` for `exists_brown_factorization`
(Lemma 1.3.1(1)) and `exists_brown_factorization_with_coprod` (Remark 1.3.2).
For a map between cofibrant objects, these supply a cofibration followed by a
weak equivalence with a trivial cofibration section. The stronger theorem also
retains the cofibration from the source–target coproduct.
The same module provides `exists_relative_factorization` (Lemma 1.3.3(1)),
extending a specified factorization across a commutative square and retaining
the cofibration from its pushout to the new factorization object.

The incremental roadmap is in [docs/formalization-plan.md](docs/formalization-plan.md).

Both use mathlib's `CategoryWithCofibrations`, `CategoryWithWeakEquivalences`,
and `IsCofibrant`. Supply `[Category C]`, the two morphism-class instances,
and `[HasInitial C]` separately. The axiom classes are propositions about those
choices; they introduce no global Lean axioms.

Pushout and factorization requirements retain their cofibrancy hypotheses.
CF5 requires coproducts of cofibrant families, not arbitrary coproducts in the
whole category. CF6 uses functors `ℕ ⥤ C` with cofibration successor maps.
Neither functorial factorizations nor general cocompleteness are assumed.

The library proves `exists_cofibrant_replacement` in the
`ABCCofibrations.ABCPrecofibrationCategory` namespace, and
`sequential_colimit_cofibrant` in `ABCCofibrations.ABCCofibrationCategory`.
`ABCCofibrations/Examples.lean` checks a model on `Type u` with both morphism
classes consisting of all maps; its instances are local.

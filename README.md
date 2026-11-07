# ABCCofibrations

Anderson–Brown–Cisinski cofibration categories, following Definition 1.1.1 of
Rădulescu-Banu, [*Cofibrations in Homotopy Theory*](https://arxiv.org/abs/math/0610009).

This is a standalone Lean project. Build it with `lake build`.

Import `ABCCofibrations.Basic` for:

- `ABCCofibrations.ABCPrecofibrationCategory C`: CF1–CF4.
- `ABCCofibrations.ABCCofibrationCategory.{w} C`: CF1–CF6, with coproducts indexed
  by `Type w`.

Import `ABCCofibrations.Coproducts` for binary coproducts of cofibrant objects
and their inclusions, together with preservation of (trivial) cofibrations when
adding a fixed cofibrant summand. These results require only CF1–CF4.

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

# Axiom correspondence: Definition 1.1.1 and the Lean classes

This note audits the classes in [Basic.lean](../ABCCofibrations/Basic.lean)
and [FibrationBasic.lean](../ABCCofibrations/FibrationBasic.lean) against
Definition 1.1.1 (and its dual) of
[*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4),
`references/radulescu-banu-2009/source/chap-cofcat.tex`, §1.1.

## Summary and differences from the paper

The Lean classes are equivalent to Definition 1.1.1. No axiom is strengthened
or weakened. The differences are in presentation only:

1. The category, the two morphism classes, and an initial object are supplied
   separately as mathlib structures (`CategoryWithCofibrations`,
   `CategoryWithWeakEquivalences`, `HasInitial`). The paper derives the
   initial object from CF1. Cofibrancy is mathlib's `IsCofibrant`, defined with
   the chosen initial object; it does not depend on that choice
   (`isCofibrant_iff_of_isInitial`).
2. CF3, CF5 and CF6 are stated for mathlib's chosen colimits, or for arbitrary
   `IsPushout` squares in CF3. The paper remarks that the representative
   does not matter. We prove this for CF5 and CF6, and CF3 is already stated
   for every pushout square.
3. The existence clause of CF5 is stated for families of cofibrant objects
   instead of families of cofibrations. The two are equivalent
   (`cf5_existence_iff`).
4. CF6 assumes only that the successive maps $a_n:A_n\to A_{n+1}$ are
   (trivial) cofibrations. As in the paper, all composites $a_{mn}$ then are
   (`cofibration_map_of_le`, `weakEquivalence_map_of_le`).
5. "Small" in CF5 is made explicit by a universe parameter `w`:
   `ABCCofibrationCategory.{w} C` requires sums indexed by `Type w`.
6. Prefibration categories (F1–F4) are *defined* as precofibration
   categories on `Cᵒᵖ`, using mathlib's opposite morphism classes. F5–F6 are
   not implemented.

## Field-by-field correspondence (CF1–CF6)

All fields are in `ABCCofibrations.ABCPrecofibrationCategory` (CF1–CF4) or
`ABCCofibrations.ABCCofibrationCategory` (CF5–CF6).

| Axiom clause (paper) | Lean field or derived result | Notes |
| --- | --- | --- |
| CF1: $\mathcal M$ has an initial object | `[HasInitial C]` | Supplied, not derived |
| CF1: the initial object is cofibrant | `initial_cofibrant` | Instance |
| CF1: cofibrations compose | `cofibrations_comp` | All cofibrations, including noncofibrant sources |
| CF1: isomorphisms are weak equivalences | `weakEquivalence_of_isIso` | |
| CF1: isomorphisms with cofibrant domain are trivial cofibrations | `cofibration_of_isIso` + `weakEquivalence_of_isIso` | Cofibration part requires `[IsCofibrant A]` |
| CF2: two out of three | `weakEquivalences_twoOutOfThree` | mathlib's `HasTwoOutOfThreeProperty` includes composition and both cancellation directions |
| CF3(1): pushout exists | `hasPushout` | $A$, $C$ cofibrant, $i$ a cofibration; instance |
| CF3(1): $j$ is a cofibration | `cofibration_of_isPushout` | For every `IsPushout` square |
| CF3(2): $j$ trivial if $i$ trivial | `weakEquivalence_of_isPushout` | For every `IsPushout` square |
| CF4: factorization $f=rf'$ for cofibrant domain | `factorization` | Existential, no functorial choice |
| CF5(1): $\coprod A_i$, $\coprod B_i$ exist | `hasCoproductOfCofibrant`, `hasCoproduct_target` | Equivalent by `cf5_existence_iff` |
| CF5(1): $\coprod A_i$, $\coprod B_i$ cofibrant | `coproduct_cofibrant` | Applies to sources and, since $B_i$ are cofibrant, to targets |
| CF5(1): $\coprod f_i$ cofibration | `coproduct_cofibration` | Any colimit cofans: `cofibration_of_isColimit` |
| CF5(2): $\coprod f_i$ trivial | `coproduct_weakEquivalence` | Any colimit cofans: `weakEquivalence_of_isColimit` |
| CF6(1): $\operatorname{colim} A_n$ exists | `hasSequentialColimit` | Indexed by `ℕ` as a preorder category |
| CF6(1): $A_0\to\operatorname{colim}A_n$ cofibration | `sequential_cofibration` | Any colimit cocone: `sequential_cofibration_of_isColimit` |
| CF6(2): trivial version | `sequential_weakEquivalence` | Any colimit cocone: `sequential_weakEquivalence_of_isColimit` |

Derived facts quoted in the paper's discussion after Definition 1.1.1:

| Paper remark | Lean |
| --- | --- |
| A cofibration with cofibrant domain has cofibrant target | `cofibrant_target` |
| Cofibrant replacements exist | `exists_cofibrant_replacement` |
| The choice of pushout representative in CF3 does not matter | CF3 fields quantify over all `IsPushout` squares |
| $\mathcal M_{cof}$ is a precofibration category | `cofibrantObject_precofibrationCategory` (`CofibrantSubcategory.lean`) |
| Colimit of a CF6 sequence is cofibrant | `sequential_colimit_cofibrant` |

## Checks requested by the audit

**Choice of initial object.** If $I$ is any initial object, then
$\bot\to I$ is an isomorphism with cofibrant domain, hence a cofibration, and
so is its inverse. Composing gives
$\mathrm{Cof}(\bot\to A)\iff\mathrm{Cof}(I\to A)$
(`isCofibrant_iff_of_isInitial`). The dual comparison of the chosen terminal
object of $\mathcal C$ with the chosen initial object of $\mathcal C^{op}$ is
`isFibrant_iff_isCofibrant_op`.

**Isomorphic representatives.** CF3 is stated for every pushout square,
which is equivalent to the chosen-pushout form by CF1, composition, and two
out of three. For CF5 and CF6 the fields use mathlib's chosen colimits; the
`…_of_isColimit` theorems extend them to every colimit cocone, by composing
with the canonical comparison isomorphisms, whose domains are cofibrant.

**The converse presentation of CF5.** Applying the paper's CF5 to identity
maps $1_{A_i}$, which are cofibrations because their domains are cofibrant,
gives existence of coproducts of cofibrant families. Conversely the targets
$B_i$ of cofibrations with cofibrant domains are cofibrant by
`cofibrant_target`, so their coproduct exists too (`cf5_existence_iff`).

**Empty, finite and countable families.** For empty $I$, the coproduct is
initial, so its cofibrancy already follows from CF1
(`isCofibrant_coproduct_of_isEmpty`); CF5 adds nothing in that case.
Finite families, in any universe, are handled from CF1–CF4 alone in
[Coproducts.lean](../ABCCofibrations/Coproducts.lean) (Lemma 1.2.1(1)), by
reindexing through `Fin n`. CF5 therefore has content only for infinite
families. A countable family is covered by `ABCCofibrationCategory.{w}` after
reindexing by `ULift.{w} ℕ`; transferring CF5 to index types that are merely
`Small.{w}` is not yet packaged and belongs to the §1.6 work.

**Universe of CF6.** The CF6 diagram is indexed by `ℕ` with its preorder
category structure, whose objects and morphisms lie in `Type 0`. This is
independent of the coproduct universe `w` and of the universes of $\mathcal M$.
[Examples.lean](../ABCCofibrations/Examples.lean) instantiates
`ABCCofibrationCategory.{u}` on `Type u`, confirming that the universe
parameters are satisfiable.

**Interaction with mathlib instances.** The class installs as instances only
CF1 cofibrancy of `⊥_ C`, composition of cofibrations, two out of three, and
CF3 existence of pushouts under its cofibrancy hypotheses. Mathlib's
instances for cofibrations of coproduct inclusions
(`ModelCategory/IsCofibrant.lean`) require unrestricted
`IsStableUnderCobaseChange`, which is never provided, so they do not fire. We
do not assert unrestricted `ContainsIdentities` or `RespectsIso` for
cofibrations. The prefibration side adds the dual instances
(`fibrations_comp`, `terminal_fibrant`, `hasPullback`, …); where both
structures are present the duplicated instances are propositions, so the
overlap is harmless.

## Prefibration categories (F1–F4)

`ABCPrefibrationCategory C` is an abbreviation for
`ABCPrecofibrationCategory Cᵒᵖ`, with mathlib's opposite classes:
cofibrations of $\mathcal C^{op}$ are opposites of fibrations, weak
equivalences are opposites of weak equivalences, and `[HasTerminal C]` gives
the initial object of $\mathcal C^{op}$. Each of F1–F4 is CF1–CF4 read in
$\mathcal C^{op}$; the native statements are proved in `FibrationBasic.lean`
(`terminal_fibrant`, `fibrations_comp`, `weakEquivalence_of_isIso`,
`fibration_of_isIso`, `weakEquivalences_twoOutOfThree`, `hasPullback`,
`fibration_of_isPullback`, `weakEquivalence_of_isPullback`, `factorization`).
F1's "isomorphisms with fibrant codomain are trivial fibrations" is CF1's
condition on the cofibrant domain in $\mathcal C^{op}$, via
`isFibrant_iff_isCofibrant_op`. F5–F6 are not formalized.

## Scope of verification

Lean checks the derived theorems named above. The correspondence of each
field with the printed axiom is a reading of the source, recorded here for
review; a successful build does not certify it.

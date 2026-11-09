# Over and under categories (§1.7)

The implementation is [OverUnder.lean](../../ABCCofibrations/OverUnder.lean).
The source is §1.7 of
[*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4)
(`references/radulescu-banu-2009/source/chap-cofcat.tex`).

## Differences from the paper

* Only the precofibration (CF1–CF4) part of Proposition 1.7.1(1) is
  formalized. The CF5–CF6 parts and the fibration statement (2) are not yet
  formalized; see *Remaining work*.
* The over and under categories are mathlib's `Over A` and `Under A`, i.e.
  $(\mathcal M\downarrow A)$ and $(A\downarrow\mathcal M)$ for the identity
  functor. The induced classes on `Over A` are mathlib's own
  (`Mathlib.AlgebraicTopology.ModelCategory.Over`). Mathlib lists those on
  `Under A` as a TODO; they are defined here in the same way, as maps whose
  underlying map lies in the class.
* The paper calls the result "a simple consequence of the definitions". The
  formal proof makes explicit the two facts it relies on: cofibrancy in the
  over and under categories, and the computation of pushouts in $\mathcal M$.

## Statement

*Let $\mathcal M$ be a precofibration category and $A$ an object. With the
induced weak equivalences and cofibrations,*

*(a) $(\mathcal M\downarrow A)$ is a precofibration category;*

*(b) if $A$ is cofibrant, $(A\downarrow\mathcal M)$ is a precofibration
category.*

## Proof outline

**Cofibrant objects.** The initial object of $(\mathcal M\downarrow A)$ is
$\varnothing\to A$, whose underlying object is initial in $\mathcal M$; so an
object $X\to A$ is cofibrant exactly when $X$ is
(`isCofibrant_over_iff`, using that cofibrancy does not depend on the chosen
initial object). The initial object of $(A\downarrow\mathcal M)$ is
$1_A$, so an object $A\xrightarrow{x}X$ is cofibrant exactly when $x$ is a
cofibration (`isCofibrant_under_iff`). This is where $A$ must be cofibrant:
CF1 asks for the initial object $1_A$ to be cofibrant. Then $X$ is cofibrant.

**Pushouts.** Both forgetful functors create pushouts: for `Under A` because
spans are connected, for `Over A` because the forgetful functor creates all
colimits that exist in $\mathcal M$. So the pushouts required by CF3 exist,
and a pushout square upstairs is a pushout square of underlying objects;
CF3 in $\mathcal M$ then gives CF3 upstairs.

**Factorization.** For $f:X\to Y$ with $X$ cofibrant, factor the underlying
map in $\mathcal M$ as $X\xrightarrow{i}Z\xrightarrow{p}Y$ and give $Z$ the
structure map $Z\to Y\to A$ (over $A$), resp. $A\to X\to Z$ (under $A$).

CF1's statements about isomorphisms and CF2 hold because isomorphisms and
two out of three are detected on underlying maps.

## Remaining work

**CF5–CF6.** Sequential colimits are connected, so they are created by both
forgetful functors, and CF6 transfers directly. Coproducts in
$(\mathcal M\downarrow A)$ are computed in $\mathcal M$, so CF5 transfers.
Coproducts in $(A\downarrow\mathcal M)$ are not coproducts in $\mathcal M$:
$\coprod_A X_i$ is the pushout of $\coprod X_i\leftarrow\coprod A\to A$. Its
existence and the CF5 properties need CF5 for $\coprod A$ together with CF3,
which is a genuine (short) argument rather than a transfer.

**Proposition 1.7.1(2).** The fibration statements are dual. With prefibration
categories defined through opposites, they should follow from (1) using
mathlib's `Over.opEquivOpUnder` and `Under.opEquivOpOver`, once the
precofibration structure is transported along an equivalence of categories
compatible with the morphism classes.

## Lean correspondence

All names are in `ABCCofibrations` or `ABCCofibrations.ABCPrecofibrationCategory`.

| Statement | Declaration |
| --- | --- |
| Induced classes on `Under A` | `underCategoryWithCofibrations`, `underCategoryWithWeakEquivalences`, `cofibration_under_iff`, `weakEquivalence_under_iff` |
| Two out of three on `Under A` | `underWeakEquivalences_twoOutOfThree` |
| Initial object of `Over A` | `overMkInitialIsInitial`, `isInitial_initial_left` |
| Cofibrant objects of `Over A` | `isCofibrant_over_iff` |
| Cofibrant objects of `Under A` | `isCofibrant_under_iff`, `isCofibrant_right_of_isCofibrant` |
| Pushouts | `hasPushout_over`, `isPushout_over_left`, `hasPushout_under` |
| Proposition 1.7.1(1)(a), CF1–CF4 | `overPrecofibrationCategory` |
| Proposition 1.7.1(1)(b), CF1–CF4 | `underPrecofibrationCategory` |

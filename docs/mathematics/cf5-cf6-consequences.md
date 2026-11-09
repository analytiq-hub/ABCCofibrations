# Elementary consequences of CF5 and CF6 (§1.6)

The implementation so far is
[SmallSums.lean](../../ABCCofibrations/SmallSums.lean). The source is
§1.6 of [*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4)
(`references/radulescu-banu-2009/source/chap-cofcat.tex`). The axioms
themselves are compared with the Lean fields in
[the axiom correspondence](../axiom-correspondence.md).

## Differences from the paper

* Lemmas 1.6.2(1) and 1.6.3(1) are proved as in the paper. The formalization
  isolates their common argument as a single statement for a fixed index type
  (below), so the finite case, the small case, and the equivalent form of CF5
  are three applications of one proof.
* "Small" means indexed by `Type w`, where `w` is the universe parameter of
  `ABCCofibrationCategory.{w}`.
* Only the cofibration statements (1) are formalized. The fibration
  statements (2) are dual; they are not yet stated natively, because F5–F6
  are not part of `ABCPrefibrationCategory`.
* Lemmas 1.6.1, 1.6.4 and 1.6.5 are not yet formalized; see *Remaining work*.

## The common argument

Fix an index type $I$. Suppose that coproducts of $I$-indexed families of
cofibrant objects exist, and that $I$-indexed sums of trivial cofibrations
with cofibrant domains are weak equivalences. Let $f_i:A_i\to B_i$ be weak
equivalences between cofibrant objects. By Brown factorization (Lemma
1.3.1(1)) write

$$
f_i=r_if'_i,\qquad r_is_i=1_{B_i},
$$

with $f'_i$ a cofibration, $r_i$ a weak equivalence and $s_i$ a trivial
cofibration. Two out of three makes $f'_i$ a trivial cofibration. The objects
$B'_i$ are cofibrant, so $\coprod B'_i$ exists, and $\coprod f'_i$ and
$\coprod s_i$ are weak equivalences by hypothesis. Since
$(\coprod r_i)(\coprod s_i)=1$, two out of three makes $\coprod r_i$ a weak
equivalence, and so is

$$
\textstyle\coprod f_i=\bigl(\coprod r_i\bigr)\bigl(\coprod f'_i\bigr).
$$

The factorizations are chosen independently for each $i$, using choice; no
functorial factorization is assumed.

## Lemma 1.6.2(1)

*If $f_i:A_i\to B_i$ is a finite (under CF1–CF4) or small (under CF5) family
of weak equivalences between cofibrant objects, then $\coprod f_i$ is a weak
equivalence.*

For finite $I$, both hypotheses of the common argument are Lemma 1.2.1(1),
already proved from CF1–CF4 in `Coproducts.lean` for finite index types in
any universe. For small $I$ they are the CF5 fields.

## Lemma 1.6.3(1)

*Assume CF1–CF4 and the existence part of CF5(1). Then CF5(2) holds if and
only if weak equivalences between cofibrant objects are stable under small
sums.*

The forward direction is the common argument; the converse holds because
the target of a cofibration with cofibrant domain is cofibrant.

## Remaining work

**Lemma 1.6.4(1)** (a map of CF6 sequences that is a weak equivalence in each
degree induces a weak equivalence of colimits) uses relative Brown
factorizations whose separate comparison maps
$B'_{n-1}\amalg_{A_{n-1}}A_n\to B'_n$ and $B'_{n-1}\amalg_{B_{n-1}}B_n\to B'_n$
are trivial cofibrations. For arbitrary vertical maps those separate claims
are false (see [the Lemma 1.3.4(1) correction](../relative-brown-factorization.md)).
In Lemma 1.6.4 the vertical maps are the sequence maps $a_n$, $b_n$, which are
cofibrations. In that case the separate comparisons are supplied by the
already proved `exists_relative_brown_of_cofibration_edges` (`Gluing.lean`):
the first comparison is a cofibration, and it is trivial by two out of three
because $f'_{n-1}$ and $f'_n$ are trivial cofibrations. So the paper's proof
of 1.6.4 goes through using the corrected statement only. Its formalization
requires an inductive construction of the factorization sequence and the
pushout tower in the second half of the proof.

**Lemma 1.6.5(1)** (equivalent forms of CF6(2)) follows from 1.6.4.

**Lemma 1.6.1(1)** (stability under small transfinite compositions implies
CF5–CF6) needs well-ordered transfinite composites; mathlib's
transfinite-composition API should be inspected first.

**Small index types.** Transfer of CF5 from `Type w` to index types that are
only `Small.{w}` is not yet packaged.

## Lean correspondence

| Statement | Declaration |
| --- | --- |
| Common argument, fixed index type | `ABCPrecofibrationCategory.weakEquivalence_sigmaMap_of_trivialCofibrations` |
| Lemma 1.6.2(1), finite | `ABCPrecofibrationCategory.weakEquivalence_coproduct_map_finite_of_weakEquivalence` |
| Lemma 1.6.2(1), small | `ABCCofibrationCategory.weakEquivalence_coproduct_map_of_weakEquivalence` |
| Lemma 1.6.3(1) | `ABCCofibrationCategory.cf5_trivial_iff` |

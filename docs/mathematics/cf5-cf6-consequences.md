# Elementary consequences of CF5 and CF6 (§1.6)

The implementation is in
[SmallSums.lean](../../ABCCofibrations/SmallSums.lean) and
[SequentialColimits.lean](../../ABCCofibrations/SequentialColimits.lean). The source is
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
* The small case of Lemma 1.6.2(1) is stated with CF5(1) and CF5(2) as
  standalone hypotheses (`CoproductCofibrationAxiom`,
  `TrivialCoproductAxiom`), so it assumes CF1–CF5 and not CF6.
* Lemmas 1.6.4(1) and 1.6.5(1) are stated with CF6(1) and CF6(2) as
  standalone hypotheses (`SequentialCofibrationAxiom`,
  `TrivialSequentialAxiom`), so they assume CF1–CF4 and CF6 only, as in the
  paper, and not CF5.
* The proof of 1.6.4(1) uses the relative Brown factorization only for
  cofibration edges, where its separate comparison claims are valid; see
  below. This is a necessary change of citation, not of statement.
* Lemma 1.6.1 is not yet formalized; see *Remaining work*.

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

## Lemma 1.6.4(1)

*Assume CF1–CF4 and CF6. Let $f_n:A_n\to B_n$ be a map of CF6 sequences
(sequences of cofibrations with $A_0$, $B_0$ cofibrant) with every $f_n$ a
weak equivalence. Then $\operatorname{colim}f_n$ is a weak equivalence
between cofibrant objects.*

A *CF6 sequence* is a functor $\mathbb N\to\mathcal M$; the transformation
$f:A\to B$ need only be natural, which the formalization checks on
successive maps (mathlib's `NatTrans.ofSequence`).

**Reedy step.** Suppose every $f_n$ is a cofibration, $f_0$ is trivial, and
every comparison $B_n\amalg_{A_n}A_{n+1}\to B_{n+1}$ is a trivial
cofibration. Put $A=\operatorname{colim}A_n$ and
$H_n=B_n\amalg_{A_n}A$. In

$$
\begin{array}{ccccc}
A_{n+1} & \to & B_n\amalg_{A_n}A_{n+1} & \to & B_{n+1}\\
\downarrow && \downarrow && \downarrow\\
A & \to & H_n & \to & H_{n+1}
\end{array}
$$

the left square and the outer rectangle are pushouts, hence so is the right
square. So $H_n\to H_{n+1}$ is a cobase change of the comparison map: a
trivial cofibration between cofibrant objects by CF3. Also $A\to H_0$ is a
cobase change of $f_0$. CF6(2) makes $H_0\to\operatorname{colim}H$ trivial.
The maps $B_n\to H_n$ and $H_n\to\operatorname{colim}B$ (induced by
$\iota_n$ and $\operatorname{colim}f$) give inverse isomorphisms
$\operatorname{colim}B\cong\operatorname{colim}H$, under which
$\operatorname{colim}f$ becomes $A\to H_0\to\operatorname{colim}H$. The
formal statement accepts any pushout representative of each comparison.

**Reduction.** Choose a strengthened Brown factorization of $f_0$ and then,
inductively, compatible ones of each $f_{n+1}$:

$$
f_n=r_nf'_n,\qquad r_ns_n=1,\qquad
b'_n:B'_n\to B'_{n+1}\text{ a cofibration},
$$

with $B'_n\amalg_{A_n}A_{n+1}\to B'_{n+1}$ and
$B'_n\amalg_{B_n}B_{n+1}\to B'_{n+1}$ trivial cofibrations. Both $f'$ and
$s$ satisfy the Reedy hypotheses, so $\operatorname{colim}f'$ and
$\operatorname{colim}s$ are weak equivalences; since
$(\operatorname{colim}r)(\operatorname{colim}s)=1$, two out of three gives
$\operatorname{colim}r$ and then $\operatorname{colim}f$.

**Use of the corrected relative Brown factorization.** The paper obtains the
inductive step from Lemma 1.3.4(1), whose separate comparison claims are
false for arbitrary vertical maps (see
[the correction](../relative-brown-factorization.md)). Here the vertical
maps $a_n$, $b_n$ are cofibrations, and
`exists_relative_brown_of_cofibration_edges` (`Gluing.lean`) supplies both
comparisons: the second is a trivial cofibration, and the first is a
cofibration which is trivial by two out of three, because $f'_n$ and the
cobase change of $f'_{n-1}$ are weak equivalences. No other part of the
argument changes.

## Lemma 1.6.5(1)

*Assume CF1–CF4 and CF6(1). The following are equivalent: (a) CF6(2);
(b) the conclusion of Lemma 1.6.4(1); (c) that conclusion when every $f_n$ is
a trivial cofibration.*

(a)⟹(b) is Lemma 1.6.4(1) and (b)⟹(c) is immediate. For (c)⟹(a), compare a
CF6 sequence of trivial cofibrations $A_n$ with the constant sequence on
$A_0$, via the maps $A_0\to A_n$; these are trivial cofibrations by
composition. The colimit of the constant sequence is $A_0$, and the induced
map is the transfinite composite $A_0\to\operatorname{colim}A_n$.

## Remaining work

**Lemma 1.6.1(1)** (stability under small transfinite compositions implies
CF5–CF6) needs well-ordered transfinite composites; mathlib's
transfinite-composition API should be inspected first.

**Small index types.** Transfer of CF5 from `Type w` to index types that are
only `Small.{w}` is not yet packaged.

**Fibration statements (2)** of Lemmas 1.6.2–1.6.5 await F5–F6.

## Lean correspondence

| Statement | Declaration |
| --- | --- |
| Common argument, fixed index type | `ABCPrecofibrationCategory.weakEquivalence_sigmaMap_of_trivialCofibrations` |
| Lemma 1.6.2(1), finite | `ABCPrecofibrationCategory.weakEquivalence_coproduct_map_finite_of_weakEquivalence` |
| CF5(1), CF5(2) as hypotheses | `ABCPrecofibrationCategory.CoproductCofibrationAxiom`, `ABCPrecofibrationCategory.TrivialCoproductAxiom` |
| Lemma 1.6.2(1), small (CF1–CF5 only) | `ABCPrecofibrationCategory.weakEquivalence_coproduct_map_of_weakEquivalence` |
| Lemma 1.6.2(1), small, in a cofibration category | `ABCCofibrationCategory.weakEquivalence_coproduct_map_of_weakEquivalence` |
| Lemma 1.6.3(1) | `ABCCofibrationCategory.cf5_trivial_iff` |
| CF6(1), CF6(2) as hypotheses | `ABCPrecofibrationCategory.SequentialCofibrationAxiom`, `ABCPrecofibrationCategory.TrivialSequentialAxiom` |
| Colimit of a CF6 sequence is cofibrant | `ABCPrecofibrationCategory.isCofibrant_colimit_of_sequence` |
| Reedy step | `ABCPrecofibrationCategory.weakEquivalence_colimMap_of_reedy` |
| Compatible Brown factorizations | `ABCPrecofibrationCategory.BrownData`, `BrownStep`, `BrownStep.nonempty` |
| Lemma 1.6.4(1) | `ABCPrecofibrationCategory.weakEquivalence_colimMap_of_sequences`, `ABCCofibrationCategory.weakEquivalence_colimMap_of_sequences` |
| Lemma 1.6.5(1) | `ABCPrecofibrationCategory.trivialSequentialAxiom_tfae` |

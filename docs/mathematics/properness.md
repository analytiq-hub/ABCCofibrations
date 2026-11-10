# Properness (§1.8)

The implementation is [Properness.lean](../../ABCCofibrations/Properness.lean)
(cofibration statements) and
[RightProperness.lean](../../ABCCofibrations/RightProperness.lean) (fibration
statements).
The source is §1.8 of
[*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4)
(`references/radulescu-banu-2009/source/chap-cofcat.tex`).

## Differences from the paper

* Definition 1.8.3(1) asks that "the pushouts exist, and the map $r'$ is
  again a weak equivalence". The formal definition `IsLeftProper` asks for the
  pushouts of $f$ along all maps, and for $r'$ to be a weak equivalence for
  **every** pair of pushout squares, not a chosen one. In a precofibration
  category the two readings agree, since isomorphisms are weak equivalences
  and weak equivalences compose. The existence of the second pushout follows
  from that of the first by pasting, so it is not a separate hypothesis.
* The category-pair setting of Definition 1.8.2 is not introduced separately:
  `IsLeftProper` only uses a class of weak equivalences
  (`CategoryWithWeakEquivalences`), so it applies to category pairs as stated,
  and the results below assume a precofibration category.
* The fibration statements (2) are obtained from the cofibration statements
  (1) in the opposite category. `IsRightProper f` is *defined* as
  `IsLeftProper f.op`, and PF as PCF in `Cᵒᵖ`; the pullback formulations of
  Definitions 1.8.1(2) and 1.8.3(2) are proved as lemmas
  (`IsRightProper.mk`, `IsRightProper.hasPullback`,
  `IsRightProper.weakEquivalence`, `RightProper.mk`, …). With this choice,
  Theorem 1.8.4(2)(d) in `Cᵒᵖ` is literally Theorem 1.8.4(1)(d).
* Theorem 1.8.4(2)(c) says "stable under pushout" in the paper; the dual of
  (1)(c), and what is proved, is stability under **pullback**. Likewise,
  Proposition 1.8.6(2) repeats "left proper" from part (1); the dual statement
  is proved.
* Propositions 1.8.6 and 1.8.7 assume a cocomplete (resp. complete) category.
  The proofs only use the pushouts (resp. pullbacks) along the map to be shown
  proper, so that existence is taken as the hypothesis instead; all other
  pushouts used exist because the maps involved are already proper.
* The elementary facts that left proper maps compose, are stable under
  pushout, and include isomorphisms are asserted without proof in the paper;
  they are proved here, since part (d) depends on them.

## Definitions

**PCF (Definition 1.8.1(1)).** A precofibration category is *left proper* if
for every cofibration $i:A\to B$ with $A$ cofibrant and every map
$r:A\to C$, the pushout exists, and the pushout $r':B\to D$ of $r$ is a weak
equivalence when $r$ is. Unlike CF3, the corner $C$ need not be cofibrant.
(`ABCPrecofibrationCategory.LeftProper`)

**Left proper maps (Definition 1.8.3(1)).** A map $f:A\to B$ is left proper
if, in every diagram of pushout squares

$$
\begin{array}{ccccc}
A & \xrightarrow{g} & C_1 & \xrightarrow{r} & C_2\\
{\scriptstyle f}\downarrow && \downarrow && \downarrow\\
B & \longrightarrow & D_1 & \xrightarrow{r'} & D_2
\end{array}
$$

with $r$ a weak equivalence, $r'$ is a weak equivalence, and pushouts along
$f$ exist. (`IsLeftProper`)

## Results

**All objects cofibrant.** A precofibration category in which every object is
cofibrant is left proper: CF3 provides the pushouts, and excision
(Lemma 1.4.2(1)) is exactly the PCF conclusion when the corner is cofibrant.
(`leftProper_of_forall_isCofibrant`)

**Theorem 1.8.4(1)(a).** In a left proper precofibration category, every
cofibration $i:A\to B$ with $A$ cofibrant is left proper. Factor
$g=s\,f_1$ by CF4 with $f_1$ a cofibration and $s$ a weak equivalence, and
push $i$ out along $f_1$ to a cofibration $i'$ with cofibrant domain. By
pushout pasting, $s$ and $rs$ are pushed along $i'$ to $s'$ and $r's'$;
PCF makes both weak equivalences, and two out of three gives $r'$.
(`isLeftProper_of_cofibration`)

**Elementary stability (stated without proof in the paper).** Left proper
maps are stable under pushout and under composition, and isomorphisms are
left proper. Stability under pushout is pasting of the square defining the
pushout with the squares in the definition. For composition, push $r$ first
along the pushout of $f$ (a weak equivalence because $f$ is left proper), then
along the pushout of $f_2$, which is a pushout of $f_2$ and hence left proper;
the second step uses the trivial square $1_P$ as the first square of the
definition. Isomorphisms are left proper because pushouts of isomorphisms are
isomorphisms and isomorphisms are weak equivalences.
(`IsLeftProper.of_isPushout`, `IsLeftProper.comp`, `isLeftProper_of_isIso`)

**Theorem 1.8.4(1)(b).** Every map $f:A\to B$ factors as a left proper map
followed by a weak equivalence. Take a cofibrant replacement
$a:A'\xrightarrow{\sim}A$, factor $fa=r_1f_1$ by CF4, and push $f_1$ out along
$a$ to $f':A\to Y$. Then $f'$ is left proper by (a) and stability under
pushout, the pushout $b':A_1\to Y$ of $a$ is a weak equivalence by PCF, and the
induced $r:Y\to B$ satisfies $rb'=r_1$, so it is a weak equivalence.
(`exists_leftProper_factorization`)

**Theorem 1.8.4(1)(c).** The pushout $j$ of a trivial left proper map $i$ along
any $f$ is trivial left proper. Factor $f=rf'$ by (b). The pushout $i'$ of
$i$ along $f'$ is a weak equivalence because $f'$ is left proper (applied with
the identity of $A$ and the weak equivalence $i$); pushing $r$ along $i'$ gives
a weak equivalence because $i$ is left proper; and $jr=r'i'$.
(`IsLeftProper.weakEquivalence_of_isPushout`)

**Theorem 1.8.4(1)(d).** With the same weak equivalences and the left proper
maps as cofibrations, $\mathcal M$ is again a precofibration category. In Lean
the new structure lives on a type synonym `LeftProperCofibrations C`, so that it
does not clash with the given cofibrations of `C`. Its initial object is that
of `C`; CF1 holds since isomorphisms are left proper and left proper maps
compose; CF3(1) is stability under pushout (pushouts of left proper maps exist
along all maps); CF3(2) is (c); CF4 is (b).
(`leftProperCofibrations_precofibrationCategory`)

**Proposition 1.8.5(1).** A weak equivalence is left proper exactly when its
pushouts along all maps exist and are weak equivalences. The forward direction
is (c); for the converse, both vertical maps in the definition are pushouts of
$i$ (the second by pasting), so two out of three gives $r'$.
(`isLeftProper_iff_of_weakEquivalence`)

**Proposition 1.8.6(1).** In a left proper precofibration category, if $gf$
is left proper and $g$ is trivial left proper, then $f$ is left proper
(given that pushouts along $f$ exist). Push the two squares for $f$ further
along $g$: the bottom map $r''$ is a weak equivalence because $gf$ is left
proper, the pushouts $g',g''$ of $g$ are weak equivalences by (1)(c), and
$r'g''=g'r''$ gives $r'$ by two out of three.
(`IsLeftProper.of_comp`)

**Proposition 1.8.7(1).** If the weak equivalences are closed under retracts,
a retract $f'$ of a left proper map $f$ is left proper (given that pushouts
along $f'$ exist), and likewise for trivial left proper maps. This needs no
precofibration structure. The paper says it "follows directly from the
definitions"; the proof makes the retraction explicit: if $f'$ is a retract of
$f$ via $A'\to A\to A'$, push $f$ along $A\to A'\xrightarrow{g}C_1$ and then
along $r$. The two pushouts of $f'$ along $g$ and $r$ are retracts of these,
so the map $r'$ for $f'$ is a retract of the corresponding map for $f$, which
is a weak equivalence.
(`IsLeftProper.of_retract`, `IsLeftProper.of_retract_of_weakEquivalence`)

**Fibration statements.** Theorem 1.8.4(2)(a)–(d) and Propositions
1.8.5(2)–1.8.7(2) follow from the statements (1) in $\mathcal C^{op}$.

## Remaining work

None of §1.8 remains. The paper notes that CF5 and CF6 need not transfer to
left proper maps; this is not a claim to formalize.

## Lean correspondence

All names are in `ABCCofibrations`, `ABCCofibrations.ABCPrecofibrationCategory`, or
`ABCCofibrations.ABCPrefibrationCategory`.

| Statement | Declaration |
| --- | --- |
| Definition 1.8.1(1), PCF | `LeftProper` |
| Definition 1.8.3(1), left proper map | `IsLeftProper` |
| All objects cofibrant implies left proper | `leftProper_of_forall_isCofibrant` |
| Theorem 1.8.4(1)(a) | `isLeftProper_of_cofibration` |
| Stability under pushout and composition; isomorphisms | `IsLeftProper.of_isPushout`, `IsLeftProper.comp`, `isLeftProper_of_isIso` |
| Theorem 1.8.4(1)(b) | `exists_leftProper_factorization` |
| Theorem 1.8.4(1)(c) | `IsLeftProper.weakEquivalence_of_isPushout` |
| Theorem 1.8.4(1)(d) | `LeftProperCofibrations`, `leftProperCofibrations_precofibrationCategory` |
| Proposition 1.8.5(1) | `isLeftProper_iff_of_weakEquivalence` |
| Proposition 1.8.6(1) | `IsLeftProper.of_comp` |
| Proposition 1.8.7(1) | `IsLeftProper.of_retract`, `IsLeftProper.of_retract_of_weakEquivalence` |
| Definition 1.8.1(2), PF | `RightProper` (with `RightProper.mk`, `.hasPullback`, `.weakEquivalence_of_isPullback`) |
| Definition 1.8.3(2), right proper map | `IsRightProper` (with `IsRightProper.mk`, `.hasPullback`, `.weakEquivalence`) |
| All objects fibrant implies right proper | `rightProper_of_forall_isFibrant` |
| Theorem 1.8.4(2)(a) | `isRightProper_of_fibration` |
| Stability under pullback and composition; isomorphisms | `IsRightProper.of_isPullback`, `IsRightProper.comp`, `isRightProper_of_isIso` |
| Theorem 1.8.4(2)(b) | `exists_rightProper_factorization` |
| Theorem 1.8.4(2)(c) | `IsRightProper.weakEquivalence_of_isPullback` |
| Theorem 1.8.4(2)(d) | `RightProperFibrations`, `rightProperFibrations_prefibrationCategory` |
| Proposition 1.8.5(2) | `isRightProper_iff_of_weakEquivalence` |
| Proposition 1.8.6(2) | `IsRightProper.of_comp` |
| Proposition 1.8.7(2) | `IsRightProper.of_retract`, `IsRightProper.of_retract_of_weakEquivalence` |

# Properness (§1.8)

The implementation is [Properness.lean](../../ABCCofibrations/Properness.lean).
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
* Only the cofibration statements (1) are formalized so far.
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

## Remaining work

Proposition 1.8.6(1) assumes cocompleteness and Proposition 1.8.7 concerns
retracts; neither is formalized yet. The paper notes that CF5 and CF6 need not
transfer to left proper maps. The fibration statements (2) are dual.

## Lean correspondence

All names are in `ABCCofibrations` or `ABCCofibrations.ABCPrecofibrationCategory`.

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

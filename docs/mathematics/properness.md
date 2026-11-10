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

## Remaining work

Theorem 1.8.4(1)(b)–(d): factorization through a left proper map followed by a
weak equivalence, stability of trivial left proper maps under pushout, and the
precofibration structure $(\mathcal M,\mathcal W,\mathcal{P}r\mathcal{C}of)$;
Propositions 1.8.5–1.8.7; the fibration statements (2).

## Lean correspondence

All names are in `ABCCofibrations` or `ABCCofibrations.ABCPrecofibrationCategory`.

| Statement | Declaration |
| --- | --- |
| Definition 1.8.1(1), PCF | `LeftProper` |
| Definition 1.8.3(1), left proper map | `IsLeftProper` |
| All objects cofibrant implies left proper | `leftProper_of_forall_isCofibrant` |
| Theorem 1.8.4(1)(a) | `isLeftProper_of_cofibration` |

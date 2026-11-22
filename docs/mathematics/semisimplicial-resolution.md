# The direct resolution of §9.5 and the initial-object obstruction

## Checked foundation

`SemisimplicialResolution.lean` constructs the category Δ′D of §9.5 of
*Cofibrations in Homotopy Theory*, math/0610009v4. Objects are finite nonempty
composable chains in D, including chains containing identity arrows. Maps are
injective order-preserving maps of indexing ordinals commuting with the labels.

The implementation reuses mathlib's `SemiSimplexCategory`, `nerve`, and category
of elements. It takes the opposite of the category of elements of the nerve
restricted to injective ordinal maps. The degree is the length of the simplex;
`resolution_isDirect` checks the direct-category axiom.

`resolutionTerminal` is the terminal projection pₜ. Its composition law and
`resolutionMap_terminal` check functoriality and naturality in D. The library
also supplies the labelled singleton, constant simplices, and a faithful functor
`resolutionConstants d` from Δ′ into Δ′D.

The native inverse resolution is constructed by duality from the direct
resolution of Dᵒᵖ, followed by taking opposites. `resolutionInitial` gives its
projection into D. This makes the variance of the inverse construction explicit.

No cofibration-category axioms are needed for these categorical constructions.
For `D : Type u` with morphisms in `Type v`, the resolution objects lie in
`Type (max u v)` and its morphisms are built from finite ordinal embeddings.

## Lemma 9.5.2(1)(a) cannot be used as stated

The paper claims that the fiber of pₜ over d has initial object the singleton
(d). Take D to be the terminal category. Its resolution is Δ′, the category of
all finite nonempty ordinals and injective order-preserving maps. In low
degrees it looks like this:

$$
[0]\;\rightrightarrows\;[1]\;\mathrel{\substack{\longrightarrow\\ \longrightarrow\\ \longrightarrow}}\;[2]\;\mathrel{\substack{\longrightarrow\\ \longrightarrow\\ \longrightarrow\\ \longrightarrow}}\;[3]\;\cdots
$$

The $n+2$ arrows $[n]\to[n+1]$ are the coface maps $\delta^0,\dots,\delta^{n+1}$,
where $\delta^i$ skips the vertex $i$. Every morphism is a composite of cofaces.
There are no degeneracies, since only injective maps are allowed.

For a general $D$, an object of $\Delta' D$ is a labelled chain
$(x_0\to x_1\to\cdots\to x_n)$, which may include identity arrows. Applying
$\delta^1$ and $\delta^0$ to the one-vertex simplex gives two maps

$$
(d)\;\overset{\delta^1}{\underset{\delta^0}{\rightrightarrows}}\;(d\xrightarrow{\ 1_d\ }d),
\qquad
p_t(\delta^1)=p_t(\delta^0)=1_d .
$$

$\delta^1$ sends the vertex to vertex 0, and $\delta^0$ sends it to vertex 1.
Both maps project to the identity of d. Thus the problem occurs both for a
strict functor fiber (maps projecting to an identity) and for the full
subcategory on objects whose terminal label is d.

More strongly, every object of Δ′ has two distinct face inclusions into the next
ordinal, so Δ′ has no initial object at all.
`SemisimplexCounterexample.lean` proves:

- `semisimplex_parallel_maps` and `semisimplex_not_isInitial`;
- `resolutionFiber_constant_not_isInitial`, for the full inverse-image category;
- `terminal_resolution_not_isInitial`, for every object of the resolution of
  the terminal category `Discrete PUnit`.

`SemisimplexContraction.lean` also supplies an explicit categorical contraction
zigzag `id → semisimplexShift ← const [0]`. It adjoins a new first vertex.
Both arrows are checked natural transformations. We have not yet connected
this zigzag to a formal statement about the geometric realization of the nerve.

This refutes the initial-object assertion. It does not refute the assertion of
contractibility of the nerve, or the statement of Proposition 9.5.4.

The proof of Proposition 9.5.4 uses the asserted initial object to construct a
natural weak equivalence from a constant diagram and to prove that this constant
diagram is Reedy cofibrant. Merely replacing “initial object” by “contractible
nerve” does not justify either of those steps.

## A separate candidate repair

`ResolutionTerminalVertex.lean` constructs `TerminalVertexResolution d`:
mark the terminal vertex of a simplex by a map from the singleton (d), and
require maps to preserve this marking. It is a full subcategory of the under
category of the singleton, rather than a full subcategory of Δ′D.

For the terminal input category, the marked objects are ordinals $[n]_\ast$
whose last vertex is marked. The morphisms are the injective monotone maps
that preserve the last vertex:

$$
[0]_\ast\;\longrightarrow\;[1]_\ast\;\rightrightarrows\;[2]_\ast\;\mathrel{\substack{\longrightarrow\\ \longrightarrow\\ \longrightarrow}}\;[3]_\ast\;\cdots
$$

Now only $\delta^0,\dots,\delta^{n}$ go from $[n]_\ast$ to $[n+1]_\ast$, because
$\delta^{n+1}$ would move the last vertex. In particular $[0]_\ast$ has exactly one
map to each $[m]_\ast$, the one onto the last vertex. Compare this with the two
arrows $[0]\rightrightarrows[1]$ in $\Delta'$.

`terminalVertexSingletonIsInitial` proves that the marked singleton is initial.
The marked category is now also checked to be direct, its terminal label is d,
and its markings give a natural map from the constant singleton diagram.
`ReedyConstantInitial.lean` proves that a constant diagram at a cofibrant object
is Reedy cofibrant on a direct category with an actual initial object, including
existence of its latching colimits. The marked category inherits this result.

However, `terminalVertexForget_not_final` in
`TerminalVertexCofinalityObstruction.lean` now proves that forgetting the marking
is not final: in the comma category under the singleton, whether a map equals
the marked inclusion is invariant under morphisms, and the two endpoint maps
into a constant edge give different values:

$$
\begin{array}{ccc}
 & (d) & \\
{\scriptstyle\delta^1}\swarrow & & \searrow{\scriptstyle\delta^0\,=\,\text{marking}}\\
(d\xrightarrow{1_d}d)_\ast & & (d\xrightarrow{1_d}d)_\ast
\end{array}
$$

No zigzag of objects under $(d)$ connects the left object to the right one.
So the comma category is disconnected. This rules out the naive ordinary
cofinality continuation, including for the terminal input category.
A restricted homotopical comparison and the Reedy restriction theorem remain
unproved. The construction is therefore a partial repair with a checked
limitation, not a completed corrected proof of §9.5.

## Contractibility without an initial object, pictured

Suppose D has a terminal object t. Then the zigzag below replaces the missing
initial object. Instead of a unique map from a singleton *into* every simplex,
each simplex $x$ maps *into* a common enlargement, which also receives the
singleton:

$$
\begin{array}{ccccc}
(x_0\to\cdots\to x_n) & \xrightarrow{\ \ \iota_x\ \ } & (x_0\to\cdots\to x_n\to t) & \xleftarrow{\ \ \tau_x\ \ } & (t).
\end{array}
$$

Here $\iota_x$ includes the old vertices $0,\dots,n$, and $\tau_x$ selects the new
vertex $n+1$. Both are natural. For any $f\colon x\to y$, write $f\ast t$ for $f$
extended by sending the new vertex to the new vertex. Then

$$
\begin{array}{ccccc}
x & \xrightarrow{\ \iota_x\ } & x\ast t & \xleftarrow{\ \tau_x\ } & (t)\\
{\scriptstyle f}\big\downarrow & & \big\downarrow{\scriptstyle f\ast t} & & \big\|\\
y & \xrightarrow{\ \iota_y\ } & y\ast t & \xleftarrow{\ \tau_y\ } & (t)
\end{array}
$$

commutes. The labels match because each arrow into $t$ is unique, and this is
the only place where terminality is used. In Lean these are `resolutionAppend`
($x\mapsto x\ast t$), `resolutionToAppend` ($\iota$) and
`resolutionSingletonToAppend` ($\tau$) in `ResolutionLabelledInsertion.lean`.
They are checked as functors and natural transformations.

For the terminal category, so that $\Delta' D=\Delta'$, the component at $[1]$ is

$$
[1]\;\xrightarrow{\ 0\mapsto 0,\ 1\mapsto 1\ }\;[2]\;\xleftarrow{\ 0\mapsto 2\ }\;[0].
$$

*Why this means "contractible".* A natural transformation $F\Rightarrow G$ is a
functor $\mathcal C\times[1]\to\mathcal C'$, so its nerve gives a homotopy
$|NF|\simeq|NG|$. The zigzag therefore gives
$\mathrm{id}\simeq\mathrm{const}_{(t)}$ on $|N\Delta' D|$. This is the standard
argument of Quillen (*Higher algebraic K-theory I*, §1). It is not formalized
here, and the formalization only needs the categorical zigzag.

*Application to the fibers.* The relevant homotopy fiber of $p_t$ over $d$ is
the comma category $p_t\downarrow d$. Its objects are chains with a map from the
last vertex to $d$:

$$
(x_0\to\cdots\to x_n\xrightarrow{\ a\ }d).
$$

This is the same data as a chain in the slice category $D/d$, which has the
terminal object $(d,1_d)$. Appending it is just "write $d$ at the end":

$$
(x_0\to\cdots\to x_n)\;\longmapsto\;(x_0\to\cdots\to x_n\xrightarrow{\ a\ }d),
$$

and the zigzag above contracts $\Delta'(D/d)$. The singleton $((d),1_d)$ is still
not initial in $p_t\downarrow d$, since both $\delta^0$ and $\delta^1$ above lie
over $1_d$. The contraction does not need it to be. The comparison
$p_t\downarrow d\cong\Delta'(D/d)$ is Lemma 9.5.1(1). It is now checked in
`ResolutionCommaComparison.lean` for general $u\colon D_1\to D_2$, as a functor
$\Delta'(u\downarrow d_2)\to(u\,p_t\downarrow d_2)$ that is fully faithful and
bijective on objects. Its explicit inverse sends
$(x_0\to\cdots\to x_n,\ a\colon u x_n\to d_2)$ to the chain whose $i$-th
structure map is $u(x_i\to x_n)\,a$. `ResolutionSliceContraction.lean`
transports the zigzag along it, giving the paper's $a^d$, $\alpha$, $\beta$ on
$p_t\downarrow d$. The inverse-side 9.5.1(2) is derived by duality in
`ResolutionCommaComparisonDual.lean`. $\Delta'$ is not invariant under
equivalences of categories, so the derivation uses that the two functors
between $(d_2\downarrow u)^{op}$ and $(u^{op}\downarrow d_2)$ are strictly
inverse to each other. The dual contraction of $d\downarrow p_i$ is transported
the same way.

## Lemma 9.5.2(1)(c): a second initial-object gap, and its repair

The paper proves that $i_d\colon p_t^{-1}(d)\to(p_t\downarrow d)$ is homotopy
right cofinal by claiming that, when the structure map of $x$ is not an
identity, $(a^d x,\alpha_x)$ is initial in $x\downarrow i_d$. That claim fails.
Take $D=\{0\to1\}$, $d=1$, $x=((0)\to 1)$, so that $a^d x=((0\to1)\xrightarrow{1}1)$.
For $y=((0\to1\xrightarrow{1}1)\xrightarrow{1}1)$ and $g$ selecting vertex 0, the new
vertex may go to either copy of 1:

$$
\begin{array}{ccc}
 & x=(0) & \\
{\scriptstyle\alpha_x}\swarrow & & \searrow{\scriptstyle g}\\
(0\to 1) & \overset{1\mapsto 1}{\underset{1\mapsto 2}{\rightrightarrows}} & (0\to1\xrightarrow{1}1)
\end{array}
$$

Both maps lie under $x$. `ResolutionFiberCounterexample.lean` checks this
(`FiberCounterexample.not_isInitial`).

What 9.5.4 actually uses is that colimits over $p_t^{-1}(d)$ and over
$p_t\downarrow d$ agree, i.e. that $i_d$ is *final*. This holds for a uniform
reason. Every object $(y,g)$ of $x\downarrow i_d$ is joined to $(a^d x,\alpha_x)$:

$$
(y,g)\xrightarrow{\ \alpha_y\ }(a^d y,\ \alpha_y g)\xleftarrow{\ a^d g\ }(a^d x,\ \alpha_x).
$$

The right-hand map lies under $x$ by naturality of $\alpha$, and $a^d$ lands in
the fiber. `ResolutionFiberFinal.lean` proves `resolutionFiber_final` and the
colimit isomorphism `resolutionFiberColimitIso`. There the fiber is the full
subcategory of $p_t\downarrow d$ on objects with identity structure map, which is
isomorphic to the paper's subcategory of $\Delta'D$.

The remaining gap in 9.5.4 is the use of an initial object $e(d)$ of
$p_t^{-1}(d)$. It is used to build the constant diagram $cX_{e(d)}\to X|_{p_t^{-1}(d)}$
and to prove that this diagram is Reedy cofibrant.

## Replacing the $e(d)$ step: a contraction lemma

The paper uses $e(d)$ only to conclude that

$$
X_{(d)}\xrightarrow{\ \iota\ }\operatorname{colim}_{p_t^{-1}(d)}X
$$

is a weak equivalence. The following lemma gives this without an initial object.
It uses only the contraction $a^d,\alpha,\beta$, which restricts to the fiber
(each $\alpha_y$ and $\beta_y$ has identity terminal component).

**Lemma K.** Let $M$ be a cofibration category, $F$ a small direct category,
$e\in F$, $A\colon F\to F$ a functor, and $\alpha\colon 1\Rightarrow A$,
$\beta\colon c_e\Rightarrow A$ natural transformations. Let $Y\colon F\to M$ be
Reedy cofibrant, with $Y(\alpha_j)$ and $Y(\beta_j)$ weak equivalences for all $j$.
Then $\iota_e\colon Y_e\to\operatorname{colim}_F Y$ is a weak equivalence.

*Proof.*

1. Factor $\varnothing\to c\,Y_e$ in the Reedy structure. This gives a Reedy
   cofibrant $Q$ and a levelwise weak equivalence $q\colon Q\to cY_e$. The map $q$
   is a cocone, so it induces $\kappa\colon\operatorname{colim}Q\to Y_e$ with
   $\kappa\,\iota^Q_e=q_e$.
2. The coproduct $Y\sqcup Q$ is Reedy cofibrant. Factor
   $[\,Y\alpha,\ Y\beta\circ q\,]\colon Y\sqcup Q\to A^*Y$ as a Reedy cofibration
   $Y\sqcup Q\rightarrowtail W$ followed by a levelwise weak equivalence
   $w\colon W\to A^*Y$. Let $a\colon Y\to W$ and $b\colon Q\to W$ be the components.
   By 2-out-of-3, $a$ and $b$ are levelwise weak equivalences, since $wa=Y\alpha$
   and $wb=Y\beta\circ q$ are.
3. The maps $W_j\xrightarrow{w_j}Y_{Aj}\xrightarrow{\iota_{Aj}}\operatorname{colim}Y$ form a
   cocone and induce $\rho\colon\operatorname{colim}W\to\operatorname{colim}Y$. On components:

$$
\rho\circ\operatorname{colim}a=\mathrm{id},
\qquad
\rho\circ\operatorname{colim}b=\iota_e\circ\kappa ,
$$

   because $\iota_{Aj}\,Y(\alpha_j)=\iota_j$ and $\iota_{Aj}\,Y(\beta_j)=\iota_e$.
4. A colimit of a levelwise weak equivalence between Reedy cofibrant diagrams is
   a weak equivalence. Hence $\operatorname{colim}a$ and $\operatorname{colim}b$
   are weak equivalences. Then $\rho$ is one by 2-out-of-3, and so is
   $\iota_e\kappa$.
5. In the composable triple

$$
Q_e\xrightarrow{\ \iota^Q_e\ }\operatorname{colim}Q\xrightarrow{\ \kappa\ }Y_e\xrightarrow{\ \iota_e\ }\operatorname{colim}Y ,
$$

   the composites $\kappa\iota^Q_e=q_e$ and $\iota_e\kappa$ are weak equivalences.
   By 2-out-of-6, $\iota_e$ is a weak equivalence. ∎

No connectedness, finiteness or initial object is used. $Y$ need only invert
the components of $\alpha$ and $\beta$. The lemma isolates the homotopical
content of "the fiber is contractible", in the elementary form available in a
cofibration category. It is the colimit counterpart of Szumiło's Lemma 1.17,
which shows that a homotopy equivalence of homotopical categories induces a
weak equivalence of diagram categories. That route would need derived
adjunctions, and this one avoids them.

A standalone explanation with diagrams is in
[contractible colimits](contractible-colimits.md).

**Formalized** as `weakEquivalence_colimit_ι_of_contraction` in
`ContractibleColimits.lean`, for any small direct $F$. The 2-out-of-6 step is
`weakEquivalence_of_twoOutOfSix`, derived from saturation.

**Ingredients available in the library.** Reedy factorization
(`reedy_factorization_small`), Reedy coproducts, homotopy invariance of Reedy
colimits (`reedyCofibrant_colimMap_weakEquivalence_small`, using CF5–CF6), and
saturation (`weakEquivalence_iff_isIso_map`, which gives 2-out-of-6).

**Applying it to 9.5.4.** Take $F=p_t^{-1}(d)$ (`ResolutionStrictFiber d`) and
$e=((d)\xrightarrow{1}d)$. Take $A$, $\alpha$, $\beta$ to be the restrictions of
$a^d,\alpha,\beta$, and $Y=X|_F$. A restricted diagram $X$ inverts maps with
identity terminal component, so $Y$ inverts $\alpha_y$ and $\beta_y$. Lemma K
then gives the weak equivalence $X_{(d)}\to\operatorname{colim}_F X$. Finality
(`resolutionFiberColimitIso`) identifies this colimit with the colimit over
$p_t\downarrow d$, which is $(\operatorname{colim}_{p_t}X)_d$.

**What remains.** The direct-category structure on $F$, universe bookkeeping,
and Lemma 9.5.3: $Y=X|_F$ must be Reedy cofibrant. The fiber is *not*
downward closed in $p_t\downarrow d$, so this does not follow formally from
Reedy cofibrancy on $p_t\downarrow d$. The paper's combinatorial induction is
still needed.

## Lemma 9.5.3 fails (informal counterexample, 2026-11-21)

Lemma 9.5.3(1) asserts that for every Reedy cofibrant $X$ on $\Delta'D$, the
restriction $X|_{p_t^{-1}(d)}$ is Reedy cofibrant. The following example
contradicts this. It is checked by hand and not yet in Lean.

**The fiber latching category.** Faces of a chain $y=(y_0\to\cdots\to y_m)$
correspond to nonempty subsets $S\subseteq\{0,\dots,m\}$. The face for $S$ is a
map of the fiber exactly when its last vertex $k=\max S$ satisfies $y_k=d$ and
$y_{k\to m}=1_d$. So the fiber latching category at $y$ is the poset of proper
subsets $S$ whose maximum lies in

$$
G=\{\,k : y_k=d,\ y_{k\to m}=1_d\,\}\ni m .
$$

The paper's proof takes $\mathbf i=\{n\}$ and $\mathbf j=\varnothing$, which treats
this as the poset of faces *containing $m$*. That agrees with the above only
when $G=\{m\}$.

**The example.** Let $D=\{a\to d\}$ and $y=(a\xrightarrow{u}d\xrightarrow{1}d)$, so
$G=\{1,2\}$. The fiber latching category at $y$ is

$$
\{1\},\ \{2\},\ \{0,1\},\ \{0,2\},\ \{1,2\},
$$

and $\{0\}$ is missing (its label is $a$). The two edges $\{0,1\}$ and $\{0,2\}$
are therefore **not** glued along vertex $0$:

$$
\begin{array}{ccccc}
 & \{0,1\} & & \{0,2\} & \\
 \nearrow & & \nwarrow\ \ \nearrow & & \nwarrow\\
\{1\} & & \{1,2\} & & \{2\}
\end{array}
\qquad(\text{no } \{0\}).
$$

Let $M$ be the category of sets, with injections as cofibrations and all maps
as weak equivalences. This is a cofibration category: CF4 factors $f\colon A\to B$
as $A\hookrightarrow A\sqcup B\to B$. Let $X$ send a chain to its set of vertices.
Its latching maps are bijections in positive degrees, so $X$ is Reedy cofibrant,
and it is trivially restricted. But the fiber latching object at $y$ has two
distinct copies of vertex $0$, coming from $\{0,1\}$ and from $\{0,2\}$. A cocone
to $\{\mathrm{true},\mathrm{false}\}$ separates them. So the latching map to the
three vertices of $y$ is not injective, and $X|_{p_t^{-1}(d)}$ is not Reedy
cofibrant.

**Consequences.** The paper's proof of 9.5.4 restricts $X$ to the fiber and
takes its colimit, and that step is not justified as written. The results
checked here remain valid, but their hypotheses must be read accordingly:

- `weakEquivalence_resolutionFiber_colimit` and
  `weakEquivalence_resolutionComma_colimit` keep the Reedy cofibrancy of the
  fiber restriction as an explicit hypothesis;
- Lemma K and finality of the fiber inclusion are unaffected.

**Possible repairs.**
1. Use the marked-terminal category $T_d$ (maps preserve the last vertex). Its
   latching categories *are* the faces containing the last vertex, so
   restriction preserves Reedy cofibrancy by the classical upper-face pushout
   argument, and $T_d$ has an initial object. What is missing is a homotopy
   comparison $\operatorname{colim}_{T_d}X\to\operatorname{colim}_{p_t\downarrow d}X$.
   Ordinary finality fails (`terminalVertexForget_not_final`), so this needs a
   homotopy-cofinality theorem for Reedy colimits.
2. Work on $p_t\downarrow d\cong\Delta'(D/d)$, where restriction of a Reedy
   cofibrant diagram *is* Reedy cofibrant (a discrete fibration; see
   `ReedyKan.lean`). There a restricted $X$ does not invert the components
   $\alpha_y$, so Lemma K does not apply directly.
3. Change the definition of "restricted" diagrams, or the indexing category,
   in the way the later literature does (Szumiło's homotopical categories
   $D[m]$, Cisinski's derivator approach).

## Literature check (2026-11-20)

A search for the lemma number, the proposition number, and errata did not locate
an explicit published correction of Lemma 9.5.2. This is a bounded search result,
not a claim that nobody has noticed the issue.

[Tobias Lenz, *Homotopy (pre)derivators of cofibration categories and
quasicategories*, AGT 18 (2018), 3601–3646](https://msp.org/agt/2018/18-6/agt-v18-n6-p12-p.pdf),
Proposition 3.1(2), cites either Rădulescu-Banu 9.5.8(1), or Cisinski 6.17ᵒᵖ
and 2.5ᵒᵖ, for the comparison induced by the direct resolution. This is useful
for locating the relevant theorem, but Lenz does not discuss the initial-object
obstruction there.

[Denis-Charles Cisinski, *Catégories dérivables*, BSMF 138 (2010),
317–393](https://www.numdam.org/item/BSMF_2010__138_3_317_0.pdf), §§6.12–6.17,
uses the same direct resolution. Lemma 6.15 explicitly refers to Rădulescu-Banu
Proposition 9.5.4 for its proof, and Theorem 6.17 uses Lemma 6.15. Consequently,
that reference chain does not provide an independent proof repairing this gap.
Theorem 6.11 likewise cites Rădulescu-Banu 9.5.5.

[Karol Szumiło, *Two Models for the Homotopy Theory of Cocomplete Homotopy
Theories*, arXiv:1411.0303v1](https://arxiv.org/pdf/1411.0303v1), Lemma 3.9,
provides an explicit homotopy equivalence D[n] → [n]. It inserts additional
vertices to obtain a functor s and natural weak equivalences id → s ← fp.
For n = 0, this is a contraction of Δ′ and avoids any initial-object claim.
Lemma 3.13 uses a related append-a-vertex construction. These provide an
independent model for the categorical contraction, but are not stated as
corrections of Lemma 9.5.2. Their general use in our formalization requires
checking the Reedy and colimit hypotheses, rather than identifying a homotopy
equivalence of categories with an ordinary colimit-preservation statement.

The published version of the contraction is cited as Lemma 3.2 of Szumiło's
*Frames in cofibration categories* by Lenz (after Corollary 3.2) and by Szumiło,
[*Homotopy theory of cocomplete quasicategories*, AGT 17 (2017),
765–791](https://msp.org/agt/2017/17-2/agt-v17-n2-p06-s.pdf), proof of Lemma 3.5.
The complete proof inspected here is the accessible arXiv version above;
the numbering differs.

## Differences from the paper and outstanding work

The direct resolution and terminal projection implement the paper's objects and
maps, retaining degenerate simplices. The inverse construction makes the
opposite on the ambient category explicit so that its projection has codomain D.

We do not formalize the false initial-object assertion. The marked-terminal
category is explicitly a different category, and its initial object is a
separate checked result. No replacement for the full proof of Proposition 9.5.4
is claimed. `ResolutionVertexInsertion.lean` now checks the operation of appending an
explicit terminal label to a finite chain, using mathlib's `WithTerminal`.
`ResolutionLabelledInsertion.lean` extends this to the whole resolution. For a
chosen terminal object t of D, `resolutionAppend` is an endofunctor of Δ′D, and
there is a natural zigzag 𝟭 ⟶ resolutionAppend ⟵ const (singleton t). The dual
statement holds for an initial object on the inverse resolution. This zigzag
is purely categorical: it applies only when the category being resolved has a
terminal object, for example a slice $D/d$, as pictured above. By itself it is not
a homotopy-colimit comparison for arbitrary diagrams.
The source correspondence for Lemma 9.5.1, its application to comma
categories, and the restricted Reedy comparisons must be checked before
advancing to the arbitrary-indexing diagram-category theorem.

The dedicated survey [direct and filtered replacements](direct-and-filtered-replacements.md)
collects both routes, their limitations, and alternatives from subdivision,
simplicial replacement, bounded diagrams, and filtered indexing categories.

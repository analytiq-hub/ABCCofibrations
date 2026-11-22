# Colimits over contractible direct categories (Lemma K)

This note explains a small lemma that replaces a broken step in the proof of
Proposition 9.5.4 of *Cofibrations in Homotopy Theory* (math/0610009v4). It
is formalized as `weakEquivalence_colimit_ι_of_contraction` in
`ABCCofibrations/ContractibleColimits.lean`.

## Why the lemma is needed

Proposition 9.5.4 compares diagrams on the direct resolution $\Delta'D$ with
diagrams on $D$. Its proof needs one fact about each fiber $p_t^{-1}(d)$ of the
terminal projection. For a diagram $X$ that is Reedy cofibrant and sends fiber
maps to weak equivalences,

$$
X_{(d)}\longrightarrow \operatorname{colim}_{p_t^{-1}(d)} X
\quad\text{is a weak equivalence.}
$$

The paper derives this from an initial object $e(d)$ of the fiber. With an
initial object, $X$ receives a map from the constant diagram at $X_{e(d)}$,
that constant diagram is Reedy cofibrant, and its colimit is $X_{e(d)}$. But
the fiber has **no** initial object: the singleton $(d)$ has two different
maps into $(d\xrightarrow{1}d)$, both lying over $1_d$ (see
[the resolution note](semisimplicial-resolution.md)).

The fiber is still *contractible* in a precise categorical sense, which is
explained next. Lemma K shows that this contractibility is enough.

## The statement

**A contraction.** Let $F$ be a category and $e$ an object of $F$. A
*contraction of $F$ onto $e$* is a functor $A\colon F\to F$ together with two
natural transformations

$$
\mathrm{id}_F\xRightarrow{\ \alpha\ }A\xLeftarrow{\ \beta\ }c_e ,
$$

where $c_e$ is the constant functor at $e$. Concretely, every object $j$ gets
two arrows into the common object $Aj$, and both are natural in $j$:

$$
\begin{array}{ccccc}
j & \xrightarrow{\ \alpha_j\ } & Aj & \xleftarrow{\ \beta_j\ } & e\\
{\scriptstyle f}\big\downarrow & & \big\downarrow{\scriptstyle Af} & & \big\|\\
k & \xrightarrow{\ \alpha_k\ } & Ak & \xleftarrow{\ \beta_k\ } & e
\end{array}
$$

An initial object $e$ gives a trivial contraction ($A=\mathrm{id}$, $\alpha=1$,
$\beta$ the unique maps). The point of a contraction is that $e$ need not map
to $j$ directly. It is enough that $j$ and $e$ both map into some $Aj$,
naturally.

**Lemma K.** Let $M$ be a cofibration category and $F$ a small direct category
with a contraction $(A,\alpha,\beta)$ onto $e$. Let $Y\colon F\to M$ be a Reedy
cofibrant diagram that sends every $\alpha_j$ and every $\beta_j$ to a weak
equivalence. Then the colimit of $Y$ exists, and the colimit inclusion

$$
\iota_e\colon Y_e\longrightarrow\operatorname{colim}_F Y
$$

is a weak equivalence.

Nothing else is assumed. $F$ need not have an initial object or be finite,
and $Y$ need not send every arrow to a weak equivalence. Only the arrows of
the contraction matter.

## Where it is applied

For the fiber $F=p_t^{-1}(d)$:

- $e=(d)$ is the one-vertex simplex at $d$;
- $A=a^d$ appends $d$ as a new last vertex: $(d_0\to\cdots\to d_n)\mapsto(d_0\to\cdots\to d_n\to d)$;
- $\alpha_y$ includes the old vertices, and $\beta_y$ selects the new last vertex.

Every $\alpha_y$ and $\beta_y$ has identity terminal component. A restricted
diagram $X$ therefore sends them to weak equivalences, and Lemma K gives the
weak equivalence $X_{(d)}\to\operatorname{colim}_{p_t^{-1}(d)}X$.

## Two facts used in the proof

1. **Colimits are homotopy invariant on Reedy cofibrant diagrams.** If $f$ is
   a levelwise weak equivalence between Reedy cofibrant diagrams on a small
   direct category, then both colimits exist and $\operatorname{colim}f$ is a
   weak equivalence. (Theorem 9.3.5(1)(c); `reedyCofibrant_colimMap_weakEquivalence_small`.)
2. **Two out of six.** Given composable maps $u,v,w$ with $vu$ and $wv$ weak
   equivalences, all of $u,v,w$ are weak equivalences. In a cofibration
   category this follows from saturation: weak equivalences are exactly the
   maps that become isomorphisms in the homotopy category
   (`weakEquivalence_of_twoOutOfSix`).

The diagram category $M^F$ with its Reedy structure is itself a cofibration
category (Theorem 9.2.4(1)(a)). So cofibrant replacements, coproducts of
cofibrant objects, and factorizations are all available there. Weak
equivalences in $M^F$ are levelwise.

## The proof

**The idea.** We cannot compare $Y$ directly with the constant diagram $c\,Y_e$,
because $c\,Y_e$ is usually not Reedy cofibrant. So its colimit has no homotopy
meaning. Instead we route both $Y$ and a cofibrant replacement of $c\,Y_e$ into
the reindexed diagram $A^*Y=Y\circ A$. Then we use the contraction to map
everything back into $\operatorname{colim}Y$.

### Step 1: replace the constant diagram

Factor $\varnothing\to c\,Y_e$ in the Reedy structure. This gives a Reedy
cofibrant diagram $Q$ and a levelwise weak equivalence

$$
q\colon Q\xrightarrow{\ \sim\ }c\,Y_e .
$$

A map into a constant diagram is the same thing as a cocone. So $q$ induces a
map out of the colimit,

$$
\kappa\colon\operatorname{colim}Q\longrightarrow Y_e,
\qquad
\kappa\circ\iota^Q_e=q_e .
$$

### Step 2: one factorization through $A^*Y$

There are two levelwise weak equivalences into $A^*Y$:

$$
Y\xrightarrow{\ Y\alpha\ }A^*Y ,
\qquad
Q\xrightarrow{\ q\ }c\,Y_e\xrightarrow{\ Y\beta\ }A^*Y .
$$

They are levelwise weak equivalences because $Y$ inverts $\alpha_j$ and
$\beta_j$. The coproduct $Y\sqcup Q$ of Reedy cofibrant diagrams is Reedy
cofibrant. Factor the combined map:

$$
Y\sqcup Q\ \rightarrowtail\ W\ \xrightarrow{\ \ w\ \ }\ A^*Y ,
\qquad w\ \text{a levelwise weak equivalence}.
$$

Write $a\colon Y\to W$ and $b\colon Q\to W$ for the two components. Then
everything commutes:

$$
\begin{array}{ccccc}
Y & \xrightarrow{\ \ a\ \ } & W & \xleftarrow{\ \ b\ \ } & Q\\
 & {\scriptstyle Y\alpha}\searrow & \big\downarrow{\scriptstyle w} & \swarrow{\scriptstyle Y\beta\,\circ\, q} & \\
 & & A^*Y & &
\end{array}
$$

By 2-out-of-3, $a$ and $b$ are levelwise weak equivalences. $W$ is Reedy
cofibrant, since it is the target of a Reedy cofibration from a Reedy
cofibrant object.

### Step 3: map back into $\operatorname{colim}Y$

For each $j$, compose $w_j$ with the colimit inclusion at $Aj$:

$$
W_j\xrightarrow{\ w_j\ }Y_{Aj}\xrightarrow{\ \iota_{Aj}\ }\operatorname{colim}Y .
$$

These maps form a cocone on $W$, because $w$ is natural and the $\iota$ form a
cocone. They induce

$$
\rho\colon\operatorname{colim}W\longrightarrow\operatorname{colim}Y .
$$

The whole proof rests on two identities, both coming from the cocone
condition for $\iota$ along an arrow of the contraction.

*Along $\alpha_j\colon j\to Aj$:* $\ \iota_{Aj}\circ Y(\alpha_j)=\iota_j$. Hence

$$
\begin{array}{ccc}
Y_j & \xrightarrow{\ a_j\ } & W_j\\
{\scriptstyle\iota_j}\big\downarrow & & \big\downarrow{\scriptstyle w_j}\\
\operatorname{colim}Y & \xleftarrow{\ \iota_{Aj}\ } & Y_{Aj}
\end{array}
\qquad\Longrightarrow\qquad
\rho\circ\operatorname{colim}a=\mathrm{id}_{\operatorname{colim}Y}.
$$

*Along $\beta_j\colon e\to Aj$:* $\ \iota_{Aj}\circ Y(\beta_j)=\iota_e$. Hence

$$
\begin{array}{ccc}
Q_j & \xrightarrow{\ b_j\ } & W_j\\
{\scriptstyle q_j}\big\downarrow & & \big\downarrow{\scriptstyle w_j}\\
Y_e & \xrightarrow{\ Y\beta_j\ } & Y_{Aj}\\
& {\scriptstyle\iota_e}\searrow & \big\downarrow{\scriptstyle\iota_{Aj}}\\
& & \operatorname{colim}Y
\end{array}
\qquad\Longrightarrow\qquad
\rho\circ\operatorname{colim}b=\iota_e\circ\kappa .
$$

### Step 4: homotopy invariance

$a$ and $b$ are levelwise weak equivalences between Reedy cofibrant diagrams.
So $\operatorname{colim}a$ and $\operatorname{colim}b$ are weak equivalences.
Now:

- $\rho\circ\operatorname{colim}a=\mathrm{id}$ is a weak equivalence, so $\rho$ is
  one by 2-out-of-3;
- therefore $\iota_e\circ\kappa=\rho\circ\operatorname{colim}b$ is a weak
  equivalence.

### Step 5: two out of six

Consider the composable triple

$$
Q_e\ \xrightarrow{\ \ \iota^Q_e\ \ }\ \operatorname{colim}Q\ \xrightarrow{\ \ \kappa\ \ }\ Y_e\ \xrightarrow{\ \ \iota_e\ \ }\ \operatorname{colim}Y .
$$

The first two-step composite is $\kappa\circ\iota^Q_e=q_e$, a weak equivalence by
Step 1. The second is $\iota_e\circ\kappa$, a weak equivalence by Step 4. By
2-out-of-6, $\iota_e$ is a weak equivalence. $\blacksquare$

## A stronger version: Lemma K′

In the application to $p_t\downarrow d$, the diagram does **not** invert the
components $\alpha_x\colon x\to a^dx$. The terminal component of $\alpha_x$ is
the structure map $x_n\to d$. It does invert the maps $A\alpha_x$, $A\beta_x$,
$\alpha_e$ and $\alpha_{Ae}$. Lemma K′ needs only these
(`weakEquivalence_colimit_ι_of_weakContraction`).

*Proof.* Factor $Y\alpha\colon Y\to A^*Y$ as $a\colon Y\rightarrowtail W$ followed by
a levelwise weak equivalence $w\colon W\to A^*Y$. Naturality of $w$ shows that
$W$ inverts $\alpha_x$ and $\beta_x$, because $A^*Y$ does. So **Lemma K applies
to $W$**, and $\iota^W_e$ is a weak equivalence. Define
$\rho\colon\operatorname{colim}W\to\operatorname{colim}Y$ as before. Then:

$$
\rho\circ\operatorname{colim}a=\mathrm{id},
\qquad
\operatorname{colim}a\circ\rho\circ\iota^W_e=\iota^W_{Ae}\circ a_{Ae}\circ w_e .
$$

The right-hand side is a weak equivalence: $\iota^W_{Ae}$ because
$\iota^W_{Ae}\circ W(\beta_e)=\iota^W_e$, and $a_{Ae}$ because
$w_{Ae}a_{Ae}=Y(\alpha_{Ae})$. Hence $\operatorname{colim}a\circ\rho$ is a weak
equivalence. With $\rho\circ\operatorname{colim}a=\mathrm{id}$, 2-out-of-6 makes
$\operatorname{colim}a$ a weak equivalence. Finally
$\operatorname{colim}a\circ\iota^Y_e=\iota^W_e\circ a_e$, where $a_e$ is a weak
equivalence because $w_ea_e=Y(\alpha_e)$. By 2-out-of-3, $\iota^Y_e$ is a weak
equivalence. $\blacksquare$

This version is what proves the key step of 9.5.4 directly on
$p_t\downarrow d$, with no fiber and no Lemma 9.5.3.

## Remarks

- **Where contractibility enters.** It is used exactly twice, in the two
  identities of Step 3. $\alpha$ makes $\rho$ a one-sided inverse of a weak
  equivalence. $\beta$ connects $\rho$ to $\iota_e$.
- **Why not compare with the constant diagram directly?** The constant diagram
  $c\,Y_e$ is Reedy cofibrant only when the latching categories of $F$ are
  empty or connected. That holds when $F$ has an initial object, which is why
  the paper's argument worked there. The replacement $Q$ removes the need.
- **Relation to the literature.** This is a colimit counterpart of Szumiło's
  Lemma 1.17 (arXiv:1411.0303), in which a homotopy equivalence of homotopical
  categories induces a weak equivalence of diagram categories. Deducing the
  colimit statement from that lemma would need derived adjunctions. The
  argument above avoids them.
- **Status for 9.5.4.** Applying Lemma K to the fiber would need Lemma 9.5.3,
  which turned out to be false. Lemma K′ on $p_t\downarrow d$ avoids the fiber
  altogether. See the [resolution note](semisimplicial-resolution.md).

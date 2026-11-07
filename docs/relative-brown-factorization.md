# Correction to Lemma 1.3.4(1): relative Brown factorization

This note proposes a corrected replacement for Lemma 1.3.4(1) of
[*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4).
It retains compatible Brown factorizations and replaces the two separate
pushout-comparison cofibration claims by a single **combined comparison
cofibration**. The counterexample below shows why the original conclusions
cannot hold for arbitrary vertical maps.

We use the paper's notation and ordinary composition: $g\circ f$ means first
$f$, then $g$. Read this file in Markdown preview to render the equations.

## Corrected statement

Let $\mathcal M$ be a precofibration category, satisfying CF1–CF4. Consider a
commutative square of cofibrant objects

$$
\begin{array}{ccc}
A_1 & \xrightarrow{f_1} & B_1 \\
{\scriptstyle a}\downarrow && \downarrow{\scriptstyle b} \\
A_2 & \xrightarrow{f_2} & B_2,
\end{array}
\qquad b\circ f_1=f_2\circ a.
$$

Suppose a strengthened Brown factorization of $f_1$ has been specified:

$$
A_1\xrightarrow{f'_1}B'_1\xrightarrow{r_1}B_1,
\qquad s_1:B_1\longrightarrow B'_1,
$$

where

$$
r_1\circ f'_1=f_1,\qquad r_1\circ s_1=\mathrm{id}_{B_1},
$$

$r_1$ is a weak equivalence, and

$$
j_1=[f'_1,s_1]:A_1\amalg B_1\longrightarrow B'_1
$$

is a cofibration. These hypotheses imply that $B'_1$ is cofibrant, $f'_1$ is
a cofibration, and $s_1$ is a trivial cofibration.

Then there exist a cofibrant object $B'_2$ and maps

$$
f'_2:A_2\longrightarrow B'_2,\qquad
r_2:B'_2\longrightarrow B_2,\qquad
s_2:B_2\longrightarrow B'_2,\qquad
b':B'_1\longrightarrow B'_2
$$

with the following properties:

1. They give a strengthened Brown factorization of $f_2$: the maps $f'_2$ and
   $j_2=[f'_2,s_2]:A_2\amalg B_2\to B'_2$ are cofibrations, $r_2$ is a weak
   equivalence, $s_2$ is a trivial cofibration, and

$$
r_2\circ f'_2=f_2,\qquad r_2\circ s_2=\mathrm{id}_{B_2}.
$$

2. The factorizations and their sections are compatible:

$$
b'\circ f'_1=f'_2\circ a,\qquad
r_2\circ b'=b\circ r_1,\qquad
b'\circ s_1=s_2\circ b.
$$

3. The canonical **combined** comparison map is a cofibration:

$$
k:P=B'_1\amalg_{A_1\amalg B_1}(A_2\amalg B_2)\longrightarrow B'_2.
$$

The pushout defining $P$ uses the maps $j_1$ and $a\amalg b$. If its structure
maps are $\ell_1:B'_1\to P$ and $\ell_2:A_2\amalg B_2\to P$, then $k$ is
characterized by

$$
k\circ\ell_1=b',\qquad k\circ\ell_2=j_2.
$$

Here $\amalg$ denotes a coproduct, and $X\amalg_T Y$ a pushout over $T$.
No cofibration hypothesis on $a$ or $b$ is needed.

The correction replaces the original claims that the two separate maps

$$
A_2\amalg_{A_1}B'_1\longrightarrow B'_2,
\qquad
B_2\amalg_{B_1}B'_1\longrightarrow B'_2
$$

are respectively a cofibration and a trivial cofibration. Those claims are
not part of the corrected conclusion.

## Proof

Finite coproducts of cofibrant objects exist and are cofibrant by
Lemma 1.2.1(1). In particular, $A_1\amalg B_1$ and $A_2\amalg B_2$ are
cofibrant. The inclusions of either summand are cofibrations.
Since $j_1$ is a cofibration, its target $B'_1$ is cofibrant. Composing
$j_1$ with the respective inclusions shows that $f'_1$ and $s_1$ are
cofibrations.
Two-out-of-three applied to $r_1s_1=\mathrm{id}_{B_1}$ shows that $s_1$ is
also a weak equivalence.

By CF3, form the pushout

$$
\begin{array}{ccc}
A_1\amalg B_1 & \xrightarrow{j_1} & B'_1 \\
{\scriptstyle a\amalg b}\downarrow && \downarrow{\scriptstyle\ell_1} \\
A_2\amalg B_2 & \xrightarrow{\ell_2} & P.
\end{array}
$$

The map $\ell_2$ is a cofibration. Consequently $P$ is cofibrant.

Set $q_2=[f_2,\mathrm{id}_{B_2}]:A_2\amalg B_2\to B_2$.
The maps $b\circ r_1:B'_1\to B_2$ and $q_2$ agree on $A_1\amalg B_1$.
Indeed, on the first summand this is the equality

$$
b\circ r_1\circ f'_1=b\circ f_1=f_2\circ a,
$$

and on the second it is $b\circ r_1\circ s_1=b$.
Thus they induce a unique map $q:P\to B_2$ satisfying

$$
q\circ\ell_1=b\circ r_1,\qquad q\circ\ell_2=q_2.
$$

Apply CF4 to $q$, whose source is cofibrant, to obtain

$$
P\xrightarrow{k}B'_2\xrightarrow{r_2}B_2,
\qquad r_2\circ k=q,
$$

with $k$ a cofibration and $r_2$ a weak equivalence. The object $B'_2$ is
cofibrant. Define

$$
j_2=k\circ\ell_2,\qquad b'=k\circ\ell_1,
\qquad f'_2=j_2\circ\iota_A,\qquad s_2=j_2\circ\iota_B,
$$

where $\iota_A$ and $\iota_B$ are the inclusions into $A_2\amalg B_2$.
Composition shows that $j_2,f'_2,s_2$ are cofibrations. By the coproduct
universal property, $j_2=[f'_2,s_2]$.

The equality $r_2j_2=q_2$ gives $r_2f'_2=f_2$ and
$r_2s_2=\mathrm{id}_{B_2}$. Since $r_2$ is a weak equivalence,
two-out-of-three makes $s_2$ a weak equivalence as well.

Finally, the pushout equation gives

$$
b'\circ j_1=j_2\circ(a\amalg b).
$$

Restriction to the two summands yields
$b'f'_1=f'_2a$ and $b's_1=s_2b$. The remaining compatibility follows from
$r_2b'=q\ell_1=br_1$. The defining equations for $k$ hold by construction,
so $k$ is the canonical combined comparison and is a cofibration. This proves
all the corrected conclusions. $\square$

## Counterexample to the original separate-comparison claim

Work in sets, with injections as cofibrations and every map as a weak
equivalence. This is a precofibration category: the empty set is cofibrant,
injections compose, isomorphisms are injections, and pushouts of injections
are injections. Two-out-of-three is automatic. For CF4, any function
$f:X\to Y$ factors as

$$
X\xrightarrow{\iota_X}X\amalg Y
  \xrightarrow{[f,\mathrm{id}_Y]}Y,
$$

whose first map is injective and whose second map is a weak equivalence.
All sets are cofibrant.

### The sets and maps, explicitly

Let $\{*\}$ be a one-element set. Choose

$$
A_1=\{0,1\},\qquad A_2=B_1=B_2=\{*\},\qquad
B'_1=\{x_0,x_1,y\}.
$$

The object $B'_1$ is the intermediate object of the **top factorization**.
It is the disjoint union of a copy of $A_1$ and a copy of $B_1$:

$$
\begin{aligned}
f'_1(0)&=x_0,& f'_1(1)&=x_1,& s_1(*)&=y,\\
r_1(x_0)&=*,& r_1(x_1)&=*,& r_1(y)&=*.
\end{aligned}
$$

The map $a:A_1\to A_2$ collapses both $0$ and $1$ to $*$.
The maps $f_1,f_2,b$ are also the unique maps with their respective domains
and codomains; in particular, $b=\mathrm{id}_{\{*\}}$.

For reference, the Lean names mean:

| Object or map | Choice |
| --- | --- |
| $A_1=\{0,1\}$ | `Bool`, the two-element type `false`, `true` |
| $A_2=B_1=B_2=\{*\}$ | `Unit`, the one-element type with element `()` |
| $B'_1=\{x_0,x_1,y\}$ | `Bool ⊕ Unit`, a disjoint union of types |
| $x_0,x_1$ | `Sum.inl false`, `Sum.inl true` |
| $y$ | `Sum.inr ()` |
| $f'_1$ | `Sum.inl`, inclusion of the first summand |
| $s_1$ | `Sum.inr`, inclusion of the second summand |

All objects are cofibrant. The top factorization has the required section;
both inclusions are injections and their combined coproduct map is an
isomorphism. The original square commutes.

### Why the claimed comparison cannot be injective

Since $b$ is the identity, the target-side pushout is $B'_1$ itself:

$$
\begin{array}{ccc}
B_1 & \xrightarrow{s_1} & B'_1 \\
{\scriptstyle \mathrm{id}}\downarrow && \downarrow{\scriptstyle \mathrm{id}} \\
B_2 & \xrightarrow{s_1} & B'_1.
\end{array}
\qquad B_2\amalg_{B_1}B'_1\cong B'_1.
$$

Thus its comparison into a proposed $B'_2$ is the map $b':B'_1\to B'_2$.
But compatibility with the source square says $b'\circ f'_1=f'_2\circ a$.
The two squares below show the routes for each element. Write $z=f'_2(*)$.
Both bottom-right corners represent the **same point** $z\in B'_2$:

$$
\begin{array}{ccc}
0\in A_1 & \xmapsto{\ f'_1\ } & x_0\in B'_1 \\
{\scriptstyle a}\downarrow && \downarrow{\scriptstyle b'} \\
*\in A_2 & \xmapsto{\ f'_2\ } & z\in B'_2
\end{array}
\qquad\qquad
\begin{array}{ccc}
1\in A_1 & \xmapsto{\ f'_1\ } & x_1\in B'_1 \\
{\scriptstyle a}\downarrow && \downarrow{\scriptstyle b'} \\
*\in A_2 & \xmapsto{\ f'_2\ } & z\in B'_2.
\end{array}
$$

The two copies of $*$ also represent the same point of $A_2$. In the upper
right corners, however, $x_0$ and $x_1$ are distinct. Following either route
around each square expresses $b'\circ f'_1=f'_2\circ a$:

$$
\begin{aligned}
b'(x_0)&=b'(f'_1(0))=f'_2(a(0))=f'_2(*),\\
b'(x_1)&=b'(f'_1(1))=f'_2(a(1))=f'_2(*).
\end{aligned}
$$

Therefore $b'(x_0)=b'(x_1)$ even though $x_0\ne x_1$.

Thus $b'$ cannot be injective. In this example, requiring the target-side
comparison to be a trivial cofibration would require it to be injective.
Consequently the separate-comparison conclusion fails for these data.

### The corrected statement is consistent with this example

Take $B'_2=\{z,w\}$, put $f'_2(*)=z$, $s_2(*)=w$, and let $r_2$ be the
unique map to $B_2=\{*\}$. Define

$$
b'(x_0)=z,\qquad b'(x_1)=z,\qquad b'(y)=w.
$$

All compatibility equations hold. The map
$[f'_2,s_2]:A_2\amalg B_2\to B'_2$ is a bijection. Since $j_1$ is also a
bijection, the combined pushout $P$ identifies with $A_2\amalg B_2$, and
its comparison $k:P\to B'_2$ is a bijection, hence a cofibration.
The corrected conclusion therefore holds even though the separate target-side
comparison $b'$ is not injective.

## Lean correspondence

The corrected statement is implemented as
`ABCPrecofibrationCategory.exists_compatible_brown_factorization` in
`ABCCofibrations/Factorization.lean`. Its proof invokes Lemma 1.3.3(1) on the
coproduct square, which performs precisely the pushout-and-factorization
construction above. Chosen coproducts and the combined pushout are explicit
instance parameters; their existence follows from Lemma 1.2.1(1) and CF3.

| Paper notation in this note | Lean theorem name for the datum |
| --- | --- |
| $B'_1$, $B'_2$ | `Z₁`, `Z₂` |
| $f'_1$, $f'_2$ | `i₁`, `i₂` |
| $r_1$, $r_2$ | `p₁`, `p₂` |
| $b'$ | `c` |
| $s_1$, $s_2$ | `s₁`, `s₂` |
| $k$ | `k` |

`ABCCofibrations/RelativeBrownObstruction.lean` verifies the counterexample's
chosen target-side pushout and proves `no_injective_compatible_map`, the
injectivity contradiction above, for every target type universe. The full
precofibration structure on sets with injections is justified mathematically
above; it has not been constructed in Lean in this repository.

Subsequent uses of the original lemma, including in the gluing argument, must
be checked against this corrected conclusion. The combined comparison does
not supply either omitted separate-comparison cofibration claim.

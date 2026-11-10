# Equivalent forms of CF3(2) and other axiom systems (Lemma 1.4.3, Chapter 2)

The implementation is in
[CF3Equivalence.lean](../../ABCCofibrations/CF3Equivalence.lean),
[CofibrantObjectCategory.lean](../../ABCCofibrations/CofibrantObjectCategory.lean),
[QuillenModelCategory.lean](../../ABCCofibrations/QuillenModelCategory.lean) and
[OtherAxiomSystems.lean](../../ABCCofibrations/OtherAxiomSystems.lean). The source is
Lemma 1.4.3 and Chapter 2 of
[*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4)
(`references/radulescu-banu-2009/source/chap-cofcat.tex`, `chap-otheraxioms.tex`).

## Differences from the paper

* Each axiom system is a Lean class whose fields follow the paper's axioms.
  Fibration versions (categories of fibrant objects, Baues and Waldhausen
  fibration categories, and the axioms without F3(2)) are defined as the
  cofibration versions on the opposite category. For Lemma 1.4.3(2) the three
  properties are also stated natively, with pullbacks, and proved equivalent
  to their opposite forms.
* The cylinder axiom CFObj4 uses mathlib's `Cylinder` with `Cylinder.IsGood`,
  relative to any chosen binary coproduct. Binary coproducts always exist in a
  category of cofibrant objects, as pushouts over the initial object.
* Mathlib's `ModelCategory` asks only for finite limits and colimits, where the
  paper's M1 asks for all of them. Proposition 2.2.4 is therefore stated in
  three parts: every mathlib model category is a precofibration and a
  prefibration category, and with small coproducts and sequential colimits
  (resp. small products and inverse sequential limits) it is a cofibration
  (resp. fibration) category.
* Mathlib already proves the lifting characterizations of Proposition 2.2.3;
  `lifting_characterizations` restates them.
* Left and right properness of a Quillen model category (§2.2) are defined
  here as `QuillenModelCategory.IsLeftProper` and `IsRightProper`.
* For Proposition 2.4.2(2)(a) the zero object of the fibrant subcategory is a
  hypothesis; the cofibrant case (1)(a) constructs it.

## Lemma 1.4.3

*Under CF1, CF2, CF3(1) and CF4, the following are equivalent: (a) CF3(2);
(b) the gluing lemma for weak equivalences; (c) excision.*

(a)⟹(b) is Lemma 1.4.1(1)(b), once CF3(2) completes the axioms to a
precofibration category. (b)⟹(c) glues identities on the cofibration side, as
in the proof of excision. (c)⟹(a): for a trivial cofibration $i$ and a map
$f=rf'$ factored by CF4, excision makes the pushout of $i$ along the
cofibration $f'$ a weak equivalence, and the pushout of $r$ along that
pushout a weak equivalence; two out of three gives the pushout of $i$
along $f$. Part (2) follows in the opposite category; fibrancy is compared
with opposite cofibrancy using only the remaining axioms.

## Proposition 2.1.2

*A category of cofibrant objects is a precofibration category; the cofibrant
objects of a precofibration category form a category of cofibrant objects;
and dually.*

Only CF4 needs proof. It follows from Brown's factorization through a
cylinder $P$ of $A$: push out $i_0$ along $f:A\to B$ to a trivial
cofibration $s:B\to B'$ with retraction $r$; then $f'=i_1F$ satisfies
$f=rf'$, and $f'$ is a cofibration because $B'$ is also the pushout of
$A\amalg A\to B\amalg A$ along the cofibration $P.i:A\amalg A\to I$, so
$B\amalg A\to B'$ is a cofibration and $f'$ is its restriction to $A$. The
converse uses Lemma 1.5.2(1) for cylinders.

## Propositions 2.2.3–2.2.5

Cofibrations and trivial cofibrations of a model category are the maps with
the left lifting property against trivial fibrations, resp. fibrations.
Hence they contain the isomorphisms, are stable under cobase change and
coproducts, and are stable under transfinite composition, which gives CF1,
CF3, CF5 and CF6 (a sequential colimit is a transfinite composition of shape
$\mathbb N$). CF4 is M5. The fibration statements follow from mathlib's
model structure on $\mathcal C^{op}$. Properness of the model category is
exactly PCF (resp. PF), without the cofibrancy restriction.

## Propositions 2.3.2 and 2.4.2

A Baues cofibration category with an initial object is a precofibration
category, and BCF3(b) is axiom PCF; BCF6 is not needed. For Waldhausen
cofibration categories, the gluing axiom applied to the identity square of
$f$ over the pushout square of a trivial cofibration $i$ along $f$ shows
that the cobase change of $i$ is a weak equivalence. With two out of three
and the cylinder axiom this makes a category of cofibrant objects, hence a
precofibration category by Proposition 2.1.2. Conversely the cofibrant
objects of a pointed precofibration category satisfy the gluing axiom by
Lemma 1.4.1(1)(b).

## Lean correspondence

| Statement | Declaration |
| --- | --- |
| CF1, CF2, CF3(1), CF4 | `PrecofibrationAxiomsWithoutCF32` |
| Lemma 1.4.3(1) | `cf32_tfae` |
| Lemma 1.4.3(2) | `f32_tfae` |
| Definition 2.1.1 | `CategoryOfCofibrantObjects`, `CategoryOfFibrantObjects` |
| Proposition 2.1.2(1) | `CategoryOfCofibrantObjects.toPrecofibrationCategory`, `cofibrantObject_categoryOfCofibrantObjects` |
| Proposition 2.1.2(2) | `CategoryOfFibrantObjects.toPrefibrationCategory`, `fibrantObject_categoryOfFibrantObjects` |
| Proposition 2.2.3 | `QuillenModelCategory.lifting_characterizations` |
| Proposition 2.2.4 | `QuillenModelCategory.precofibrationCategory`, `prefibrationCategory`, `cofibrationCategory`, `fibrationCategory` |
| Proposition 2.2.5 | `QuillenModelCategory.leftProper`, `rightProper` |
| Definition 2.3.1 | `BauesCofibrationCategory`, `BauesFibrationCategory` |
| Proposition 2.3.2(1) | `BauesCofibrationCategory.toPrecofibrationCategory`, `BauesCofibrationCategory.leftProper` |
| Proposition 2.3.2(2) | `BauesFibrationCategory.toPrefibrationCategory`, `BauesFibrationCategory.rightProper` |
| Definition 2.4.1 | `WaldhausenCofibrationCategory`, `WaldhausenFibrationCategory` |
| Proposition 2.4.2(1)(a) | `cofibrantObject_waldhausen` |
| Proposition 2.4.2(1)(b) | `WaldhausenCofibrationCategory.toPrecofibrationCategory` |
| Proposition 2.4.2(2)(a) | `fibrantObject_waldhausen` |
| Proposition 2.4.2(2)(b) | `WaldhausenFibrationCategory.toPrefibrationCategory` |

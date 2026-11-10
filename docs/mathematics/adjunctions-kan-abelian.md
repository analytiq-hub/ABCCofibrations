# Adjunctions, Kan extensions, and abelian lemmas (§3.2, Chapter 4)

The implementation is in
[AdjunctionKan.lean](../../ABCCofibrations/AdjunctionKan.lean) and
[AbelianLemmas.lean](../../ABCCofibrations/AbelianLemmas.lean). The source is
§3.2 and Chapter 4 of
[*Cofibrations in Homotopy Theory*, v4](https://arxiv.org/abs/math/0610009v4)
(`chap-examples.tex`, `chap-kanext.tex`).

## Differences from the paper

* **Kan extension terminology.** Definition 4.3.1 calls a pair
  $(L,\varepsilon:L\gamma\Rightarrow u)$ with the terminal universal property a
  *left* Kan extension of $u$ along $\gamma$. Mathlib calls this a *right* Kan
  extension (`Functor.IsRightKanExtension`), and dually. Each statement below
  uses mathlib's notion and says which of the paper's it is. This is the same
  convention as [the derived-functor note](derived-functors.md).
* The results of this part are classical and mostly short consequences of
  mathlib's adjunction and Kan extension API. They are stated in the paper's
  form; Corollary 4.3.4 is mathlib's `hasRightExtension_iff_postcomp₁` and
  `isRightKanExtension_iff_postcomp₁` applied to an equivalence.
* Lemma 3.2.2 is stated for arbitrary pushout and pullback representatives
  (`IsPushout`, `IsPullback`). Lemma 3.2.6 holds for any adjunction, not only
  between abelian categories: a left adjoint preserves finite colimits and a
  right adjoint finite limits, which is right (left) exactness for additive
  functors between abelian categories.

## Proofs

**Proposition 4.2.1.** (1) The triangle identities characterize the
unit/counit pairs of adjunctions, which are determined by them
(`Adjunction.mkOfUnitCounit`). (2) A left (right) adjoint is fully faithful
iff the unit (counit) is an isomorphism; both are isomorphisms iff the
functors are inverse equivalences.

**Proposition 4.2.2.** If the adjoint of every map $u_1A\to B$ being an
isomorphism forces the map to be one, apply this to the counit (whose adjoint
is an identity) to make the counit an isomorphism; conversely a map is
$\psi_B\circ u_1(g)$ for its adjoint $g$. Dually for the unit, and the two
together give inverse equivalences.

**Proposition 4.3.2.** For $\gamma'\dashv\gamma$, a transformation
$G\gamma\Rightarrow u$ corresponds to $G\Rightarrow G\gamma\gamma'\Rightarrow
u\gamma'$ via the unit; the triangle identities give existence and
uniqueness of factorizations through $u\psi:u\gamma'\gamma\Rightarrow u$.

**Proposition 4.3.3.** Given a Kan extension $(F',\alpha)$ of $u$ along
$\gamma$, transformations $G\gamma'\Rightarrow F'$ correspond to
transformations $G\gamma'\gamma\Rightarrow u$. So $(G,\beta)$ is a Kan
extension of $F'$ along $\gamma'$ iff $(G,\beta\star\alpha)$ is one of $u$
along $\gamma'\gamma$, and existence of either implies existence of the other.

**Lemma 3.2.2.** Pushouts of epimorphisms and pullbacks of monomorphisms
behave well in any category. Conversely, if the pushout $f'$ of $f$ is epic
and $qf=0$, the map induced by $(q,0)$ on the pushout vanishes after $f'$,
hence vanishes, so $q=0$; this shows $f$ is epic. Pushouts of monics are
monic by mathlib's `Abelian.mono_pushout_of_mono_f`, transported to any
representative. Dually for pullbacks.

## Lean correspondence

| Statement | Declaration |
| --- | --- |
| Proposition 4.2.1(1) | `existsUnique_adjunction_iff` |
| Proposition 4.2.1(2)(a) | `full_faithful_left_iff`, `full_faithful_right_iff` |
| Proposition 4.2.1(2)(b) | `inverse_equivalences_iff` |
| Proposition 4.2.2 | `isIso_iff_isIso_homEquiv_iff`, `isIso_of_isIso_homEquiv_iff`, `isIso_homEquiv_of_isIso_iff` |
| Proposition 4.3.2(1), (2) | `isRightKanExtension_of_isLeftAdjoint`, `isLeftKanExtension_of_isRightAdjoint` |
| Proposition 4.3.3(1) | `isRightKanExtension_comp_iff`, `hasRightKanExtension_comp_iff` |
| Proposition 4.3.3(2) | `isLeftKanExtension_comp_iff`, `hasLeftKanExtension_comp_iff` |
| Corollary 4.3.4(1) | `hasRightKanExtension_comp_equivalence_iff`, `isRightKanExtension_comp_equivalence_iff` |
| Corollary 4.3.4(2) | `hasLeftKanExtension_comp_equivalence_iff`, `isLeftKanExtension_comp_equivalence_iff` |
| Lemma 3.2.2(1)–(4) | `IsPushout.epi_iff`, `IsPushout.mono_of_mono`, `IsPullback.mono_iff`, `IsPullback.epi_of_epi` |
| Lemma 3.2.6 | `Adjunction.rightExact_leftExact` |

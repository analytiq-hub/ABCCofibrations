/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Approximation functors and the approximation theorem (§5.4–§5.5)

Definition 5.4.1 (left and right approximations), Lemma 5.4.2, Theorem 5.5.1
(the approximation theorem), and Corollaries 5.5.3 and 5.5.4.

A *category pair functor* is a mathlib `LocalizerMorphism Φ : W' ⟶ W`, and the
classes of weak equivalences are multiplicative (`MorphismProperty.IsMultiplicative`),
as for the paper's category pairs. The homotopy category of `(M', W')` is any
localization `L' : M' ⥤ H'`; axiom LAP2(2) is stated in `H'`.

The paper proves the approximation theorem by an explicit construction on
zig-zags. Here the quasi-inverse of `ho t` is obtained instead by lifting a
functor `M ⥤ ho M'` through the localization of `M`; its well-definedness and
functoriality come from LAP2(2), and the two natural isomorphisms are checked
after precomposition with the localization functors.

Right approximations are left approximations of the opposite localizer
morphism (`RightApproximation`), and their results follow by duality.
-/

@[expose] public section

open CategoryTheory Category Localization

namespace ABCCofibrations

variable {M' M : Type*} [Category M'] [Category M] {W' : MorphismProperty M'}
  {W : MorphismProperty M} (Φ : LocalizerMorphism W' W)

/-- The data of axiom LAP2(1) for maps `f : tA' ⟶ B` and `p : tB' ⟶ B`:
maps `A' ⟶ D' ⟵ B'`, the second a weak equivalence, and a weak equivalence
`σ : tD' ⟶ B` making the diagram commute. -/
structure FactorizationData {A' B' : M'} {B : M} (f : Φ.functor.obj A' ⟶ B)
    (p : Φ.functor.obj B' ⟶ B) where
  /-- The middle object. -/
  D : M'
  /-- The map from `A'`. -/
  i : A' ⟶ D
  /-- The weak equivalence from `B'`. -/
  j : B' ⟶ D
  /-- The comparison weak equivalence. -/
  σ : Φ.functor.obj D ⟶ B
  hj : W' j
  hσ : W σ
  fac_i : Φ.functor.map i ≫ σ = f
  fac_j : Φ.functor.map j ≫ σ = p

namespace FactorizationData

variable {Φ} {H' : Type*} [Category H'] (L' : M' ⥤ H') [L'.IsLocalization W']

/-- The map `j⁻¹ ∘ i` in the homotopy category of `M'`. -/
noncomputable def hom {A' B' : M'} {B : M} {f : Φ.functor.obj A' ⟶ B}
    {p : Φ.functor.obj B' ⟶ B} (d : FactorizationData Φ f p) : L'.obj A' ⟶ L'.obj B' :=
  L'.map d.i ≫ (isoOfHom L' W' d.j d.hj).inv

end FactorizationData

variable {H' : Type*} [Category H'] (L' : M' ⥤ H') [L'.IsLocalization W']

/-- **Definition 5.4.1.** A left approximation (axioms LAP1, LAP2). -/
structure LeftApproximation : Prop where
  /-- LAP1. -/
  exists_resolution (A : M) : ∃ (A' : M') (p : Φ.functor.obj A' ⟶ A), W p
  /-- LAP2(1). -/
  nonempty_factorizationData {A' B' : M'} {B : M} (f : Φ.functor.obj A' ⟶ B)
    (p : Φ.functor.obj B' ⟶ B) (hp : W p) : Nonempty (FactorizationData Φ f p)
  /-- LAP2(2). -/
  hom_eq {A' B' : M'} {B : M} {f : Φ.functor.obj A' ⟶ B} {p : Φ.functor.obj B' ⟶ B}
    (d₁ d₂ : FactorizationData Φ f p) : d₁.hom L' = d₂.hom L'

section Comparison

variable {Φ L'} {H : Type*} [Category H] (L : M ⥤ H) [L.IsLocalization W] (T : H' ⥤ H)
  [CatCommSq Φ.functor L' L T]

omit [L.IsLocalization W] in
/-- Under `ho t`, the map `j⁻¹i` of a factorization becomes `p⁻¹f`. -/
lemma FactorizationData.map_hom_comp {A' B' : M'} {B : M} {f : Φ.functor.obj A' ⟶ B}
    {p : Φ.functor.obj B' ⟶ B} (d : FactorizationData Φ f p) :
    T.map (d.hom L') ≫ (CatCommSq.iso Φ.functor L' L T).inv.app B' ≫ L.map p =
      (CatCommSq.iso Φ.functor L' L T).inv.app A' ≫ L.map f := by
  let e := CatCommSq.iso Φ.functor L' L T
  have nat {X Y : M'} (u : X ⟶ Y) :
      T.map (L'.map u) ≫ e.inv.app Y = e.inv.app X ≫ L.map (Φ.functor.map u) :=
    e.inv.naturality u
  have := Localization.inverts L' W' d.j d.hj
  have hj : T.map (isoOfHom L' W' d.j d.hj).inv ≫ e.inv.app B' ≫ L.map p =
      e.inv.app d.D ≫ L.map d.σ := by
    rw [← cancel_epi (T.map (L'.map d.j)), ← T.map_comp_assoc, isoOfHom_hom_inv_id, T.map_id,
      id_comp, reassoc_of% (nat d.j), ← L.map_comp, d.fac_j]
  change T.map (L'.map d.i ≫ _) ≫ _ = _
  rw [T.map_comp, assoc, hj, reassoc_of% (nat d.i), ← L.map_comp, d.fac_i]

end Comparison

namespace LeftApproximation

variable {Φ L'} (h : LeftApproximation Φ L')

include h in
/-- Two factorizations sharing the weak equivalence from `B'` agree in the
homotopy category of `M'`. -/
lemma map_eq {A' B' D : M'} {B : M} {f : Φ.functor.obj A' ⟶ B} {p : Φ.functor.obj B' ⟶ B}
    (i₁ i₂ : A' ⟶ D) (j : B' ⟶ D) (σ : Φ.functor.obj D ⟶ B) (hj : W' j) (hσ : W σ)
    (h₁ : Φ.functor.map i₁ ≫ σ = f) (h₂ : Φ.functor.map i₂ ≫ σ = f)
    (hjσ : Φ.functor.map j ≫ σ = p) : L'.map i₁ = L'.map i₂ :=
  (cancel_mono _).1 (h.hom_eq ⟨D, i₁, j, σ, hj, hσ, h₁, hjσ⟩ ⟨D, i₂, j, σ, hj, hσ, h₂, hjσ⟩)

include h in
private lemma exists_right_inverse {A' C' : M'} (g : A' ⟶ C') {B : M}
    (p : Φ.functor.obj A' ⟶ B) (q : Φ.functor.obj C' ⟶ B) (hp : W p)
    (w : Φ.functor.map g ≫ q = p) :
    ∃ (E : M') (k : C' ⟶ E) (l : A' ⟶ E) (τ : Φ.functor.obj E ⟶ B), W' l ∧ W τ ∧
      Φ.functor.map k ≫ τ = q ∧ L'.map g ≫ L'.map k = L'.map l := by
  obtain ⟨d⟩ := h.nonempty_factorizationData q p hp
  refine ⟨d.D, d.i, d.j, d.σ, d.hj, d.hσ, d.fac_i, ?_⟩
  rw [← L'.map_comp]
  exact h.map_eq (g ≫ d.i) d.j d.j d.σ d.hj d.hσ (by rw [Functor.map_comp, assoc, d.fac_i, w])
    d.fac_j d.fac_j

include h in
/-- **Lemma 5.4.2(1).** For a left approximation `t`, if `q ∘ t(f) = p` with
`p, q` weak equivalences, then `f` becomes an isomorphism in the homotopy
category of `M'`. -/
theorem isIso_map {A' C' : M'} (g : A' ⟶ C') {B : M} (p : Φ.functor.obj A' ⟶ B)
    (q : Φ.functor.obj C' ⟶ B) (hp : W p) (hq : W q) (w : Φ.functor.map g ≫ q = p) :
    IsIso (L'.map g) := by
  obtain ⟨E, k, l, τ, hl, hτ, hk, hgk⟩ := h.exists_right_inverse g p q hp w
  obtain ⟨E₂, k₂, l₂, τ₂, hl₂, -, -, hkk⟩ := h.exists_right_inverse k q τ hq hk
  have := Localization.inverts L' W' l hl
  have := Localization.inverts L' W' l₂ hl₂
  have h₁ : (inv (L'.map l) ≫ L'.map g) ≫ L'.map k = 𝟙 _ := by
    rw [assoc, hgk, IsIso.inv_hom_id]
  have h₂ : L'.map k ≫ (L'.map k₂ ≫ inv (L'.map l₂)) = 𝟙 _ := by
    rw [← assoc, hkk, IsIso.hom_inv_id]
  have : IsIso (L'.map k) := by
    refine ⟨L'.map k₂ ≫ inv (L'.map l₂), h₂, ?_⟩
    calc (L'.map k₂ ≫ inv (L'.map l₂)) ≫ L'.map k
        = ((inv (L'.map l) ≫ L'.map g) ≫ L'.map k) ≫ (L'.map k₂ ≫ inv (L'.map l₂)) ≫
            L'.map k := by rw [h₁, id_comp]
      _ = (inv (L'.map l) ≫ L'.map g) ≫ (L'.map k ≫ (L'.map k₂ ≫ inv (L'.map l₂))) ≫
            L'.map k := by simp only [assoc]
      _ = 𝟙 _ := by rw [h₂, id_comp, h₁]
  rw [show L'.map g = L'.map l ≫ inv (L'.map k) by rw [← hgk, assoc, IsIso.hom_inv_id, comp_id]]
  infer_instance

section Construction

/-- The chosen object `C(A)` of LAP1. -/
noncomputable def obj (A : M) : M' := (h.exists_resolution A).choose

/-- The chosen weak equivalence `p_A : tC(A) ⟶ A` of LAP1. -/
noncomputable def res (A : M) : Φ.functor.obj (h.obj A) ⟶ A :=
  (h.exists_resolution A).choose_spec.choose

lemma res_mem (A : M) : W (h.res A) := (h.exists_resolution A).choose_spec.choose_spec

/-- The chosen factorization data of a map `f`, relative to the chosen
resolutions. -/
noncomputable def data {A B : M} (f : A ⟶ B) : FactorizationData Φ (h.res A ≫ f) (h.res B) :=
  (h.nonempty_factorizationData _ _ (h.res_mem B)).some

variable [W'.IsMultiplicative] [W.IsMultiplicative]

/-- The functor `M ⥤ ho M'` sending `A` to `C(A)` and `f` to `j(f)⁻¹ ∘ i(f)`. -/
noncomputable def functor : M ⥤ H' where
  obj A := L'.obj (h.obj A)
  map f := (h.data f).hom L'
  map_id A := by
    rw [h.hom_eq (h.data (𝟙 A)) ⟨h.obj A, 𝟙 _, 𝟙 _, h.res A, W'.id_mem _, h.res_mem A,
      by simp, by simp⟩]
    simp [FactorizationData.hom, isoOfHom_id_inv]
  map_comp {A B E} f g := by
    let df := h.data f
    let dg := h.data g
    obtain ⟨e⟩ := h.nonempty_factorizationData (df.σ ≫ g) dg.σ dg.hσ
    let c : FactorizationData Φ (h.res A ≫ f ≫ g) (h.res E) :=
      ⟨e.D, df.i ≫ e.i, dg.j ≫ e.j, e.σ, W'.comp_mem _ _ dg.hj e.hj, e.hσ,
        by rw [Functor.map_comp, assoc, e.fac_i, ← assoc, df.fac_i, assoc],
        by rw [Functor.map_comp, assoc, e.fac_j, dg.fac_j]⟩
    have key : L'.map (df.j ≫ e.i) = L'.map (dg.i ≫ e.j) :=
      h.map_eq (f := h.res B ≫ g) (p := h.res E) _ _ (dg.j ≫ e.j) e.σ
        (W'.comp_mem _ _ dg.hj e.hj) e.hσ
        (by rw [Functor.map_comp, assoc, e.fac_i, ← assoc, df.fac_j])
        (by rw [Functor.map_comp, assoc, e.fac_j, dg.fac_i])
        (by rw [Functor.map_comp, assoc, e.fac_j, dg.fac_j])
    change (h.data (f ≫ g)).hom L' = df.hom L' ≫ dg.hom L'
    rw [h.hom_eq (h.data (f ≫ g)) c]
    simp only [FactorizationData.hom, c, Iso.comp_inv_eq, isoOfHom_hom, assoc]
    rw [L'.map_comp dg.j e.j, isoOfHom_inv_hom_id_assoc, ← L'.map_comp, ← key]
    simp

lemma functor_inverts : W.IsInvertedBy h.functor := fun A B f hf ↦ by
  have := h.isIso_map (h.data f).i (h.res A ≫ f) (h.data f).σ
    (W.comp_mem _ _ (h.res_mem A) hf) (h.data f).hσ (h.data f).fac_i
  change IsIso ((h.data f).hom L')
  unfold FactorizationData.hom
  infer_instance

omit [W'.IsMultiplicative] [W.IsMultiplicative] in
include h in
/-- **Theorem 5.5.1** (the approximation theorem), for left approximations: a
left approximation induces an equivalence of homotopy categories. -/
theorem isLocalizedEquivalence [W'.IsMultiplicative] [W.IsMultiplicative] :
    Φ.IsLocalizedEquivalence := by
  let L := W.Q
  let T := Φ.localizedFunctor L' L
  let e := CatCommSq.iso Φ.functor L' L T
  let S := Localization.lift h.functor h.functor_inverts L
  let φ : h.functor ⋙ T ≅ L := NatIso.ofComponents
    (fun A ↦ e.symm.app (h.obj A) ≪≫ isoOfHom L W (h.res A) (h.res_mem A))
    (fun {A B} f ↦ by
      change T.map ((h.data f).hom L') ≫ (e.inv.app (h.obj B) ≫ L.map (h.res B)) =
        (e.inv.app (h.obj A) ≫ L.map (h.res A)) ≫ L.map f
      rw [assoc, ← L.map_comp]
      exact (h.data f).map_hom_comp L T)
  let dd (A' : M') : FactorizationData Φ (h.res (Φ.functor.obj A')) (𝟙 (Φ.functor.obj A')) :=
    (h.nonempty_factorizationData _ _ (W.id_mem _)).some
  have hdd (A' : M') : IsIso ((dd A').hom L') := by
    have := h.isIso_map (dd A').i (h.res _) (dd A').σ (h.res_mem _) (dd A').hσ (dd A').fac_i
    unfold FactorizationData.hom
    infer_instance
  let ψ : Φ.functor ⋙ h.functor ≅ L' :=
    NatIso.ofComponents (fun A' ↦ @asIso _ _ _ _ ((dd A').hom L') (hdd A'))
    (fun {A' B'} g ↦ by
      let dA := dd A'
      let dB := dd B'
      let dg := h.data (Φ.functor.map g)
      change dg.hom L' ≫ dB.hom L' = dA.hom L' ≫ L'.map g
      obtain ⟨x⟩ := h.nonempty_factorizationData (dA.σ ≫ Φ.functor.map g)
        (𝟙 (Φ.functor.obj B')) (W.id_mem _)
      let QR : FactorizationData Φ (h.res (Φ.functor.obj A') ≫ Φ.functor.map g)
          (𝟙 (Φ.functor.obj B')) :=
        ⟨x.D, dA.i ≫ x.i, x.j, x.σ, x.hj, x.hσ,
          by rw [Functor.map_comp, assoc, x.fac_i, ← assoc, dA.fac_i], x.fac_j⟩
      have keyR : L'.map (dA.j ≫ x.i) = L'.map (g ≫ x.j) :=
        h.map_eq (f := Φ.functor.map g) (p := 𝟙 _) _ _ x.j x.σ x.hj x.hσ
          (by rw [Functor.map_comp, assoc, x.fac_i, ← assoc, dA.fac_j, id_comp])
          (by rw [Functor.map_comp, assoc, x.fac_j, comp_id]) x.fac_j
      have hR : dA.hom L' ≫ L'.map g = QR.hom L' := by
        simp only [FactorizationData.hom, QR, Iso.eq_comp_inv, isoOfHom_hom, assoc]
        rw [← L'.map_comp g x.j, ← keyR, L'.map_comp, isoOfHom_inv_hom_id_assoc,
          ← L'.map_comp]
      obtain ⟨y⟩ := h.nonempty_factorizationData dg.σ dB.σ dB.hσ
      let QL : FactorizationData Φ (h.res (Φ.functor.obj A') ≫ Φ.functor.map g)
          (𝟙 (Φ.functor.obj B')) :=
        ⟨y.D, dg.i ≫ y.i, dB.j ≫ y.j, y.σ, W'.comp_mem _ _ dB.hj y.hj, y.hσ,
          by rw [Functor.map_comp, assoc, y.fac_i, dg.fac_i],
          by rw [Functor.map_comp, assoc, y.fac_j, dB.fac_j]⟩
      have keyL : L'.map (dg.j ≫ y.i) = L'.map (dB.i ≫ y.j) :=
        h.map_eq (f := h.res (Φ.functor.obj B')) (p := 𝟙 _) _ _ (dB.j ≫ y.j) y.σ
          (W'.comp_mem _ _ dB.hj y.hj) y.hσ
          (by rw [Functor.map_comp, assoc, y.fac_i, dg.fac_j])
          (by rw [Functor.map_comp, assoc, y.fac_j, dB.fac_i])
          (by rw [Functor.map_comp, assoc, y.fac_j, dB.fac_j])
      have hL : dg.hom L' ≫ dB.hom L' = QL.hom L' := by
        simp only [FactorizationData.hom, QL, Iso.eq_comp_inv, isoOfHom_hom, assoc]
        rw [L'.map_comp dB.j, isoOfHom_inv_hom_id_assoc, ← L'.map_comp dB.i, ← keyL,
          L'.map_comp, isoOfHom_inv_hom_id_assoc, ← L'.map_comp]
      rw [hL, hR, h.hom_eq QL QR])
  let e₁ : S ⋙ T ≅ 𝟭 _ := liftNatIso L W (L ⋙ S ⋙ T) L (S ⋙ T) (𝟭 _)
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (Localization.fac _ _ L) T ≪≫ φ)
  let e₂ : T ⋙ S ≅ 𝟭 _ := liftNatIso L' W' (L' ⋙ T ⋙ S) L' (T ⋙ S) (𝟭 _)
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.symm S ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Localization.fac _ _ L) ≪≫ ψ)
  have : T.IsEquivalence := (CategoryTheory.Equivalence.mk T S e₂.symm e₁).isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' Φ L' L T

end Construction

end LeftApproximation

omit [L'.IsLocalization W'] in
/-- **Corollary 5.5.3(1).** A localizer morphism is a left approximation iff it
satisfies LAP1 and LAP2(1) and induces an equivalence of homotopy categories. -/
theorem leftApproximation_iff [W'.IsMultiplicative] [W.IsMultiplicative]
    [L'.IsLocalization W'] :
    LeftApproximation Φ L' ↔
      (∀ A : M, ∃ (A' : M') (p : Φ.functor.obj A' ⟶ A), W p) ∧
      (∀ {A' B' : M'} {B : M} (f : Φ.functor.obj A' ⟶ B) (p : Φ.functor.obj B' ⟶ B),
        W p → Nonempty (FactorizationData Φ f p)) ∧ Φ.IsLocalizedEquivalence := by
  refine ⟨fun h ↦ ⟨h.exists_resolution, h.nonempty_factorizationData,
    h.isLocalizedEquivalence⟩, fun ⟨h₁, h₂, _⟩ ↦ ⟨h₁, h₂, fun {A' B' B f p} d₁ d₂ ↦ ?_⟩⟩
  let L := W.Q
  let T := Φ.localizedFunctor L' L
  have hp : W p := by
    rw [← d₁.fac_j]
    exact W.comp_mem _ _ (Φ.map _ d₁.hj) d₁.hσ
  have := Localization.inverts L W p hp
  apply T.map_injective
  rw [← cancel_mono ((CatCommSq.iso Φ.functor L' L T).inv.app B' ≫ L.map p),
    d₁.map_hom_comp L T, d₂.map_hom_comp L T]

/-- If the opposite localizer morphism induces an equivalence of homotopy
categories, so does the localizer morphism. -/
theorem isLocalizedEquivalence_of_op [Φ.op.IsLocalizedEquivalence] :
    Φ.IsLocalizedEquivalence := by
  let G := Φ.localizedFunctor W'.Q W.Q
  let : CatCommSq Φ.op.functor W'.Q.op W.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W'.Q W.Q G).symm⟩
  have : G.op.IsEquivalence := Φ.op.isEquivalence W'.Q.op W.Q.op G.op
  have : G.IsEquivalence := (G.op.asEquivalence.unop).isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' Φ W'.Q W.Q G

/-- **Definition 5.4.1**, right approximations (axioms RAP1, RAP2): left
approximations of the opposite localizer morphism. RAP1 asks for weak
equivalences `A ⟶ tA'`, and RAP2 for factorizations `A ⟶ tS' ⟶ tB'` of maps
`A ⟶ tB'` relative to weak equivalences `A ⟶ tA'`, unique in `ho M'`. -/
abbrev RightApproximation : Prop := LeftApproximation Φ.op L'.op

namespace RightApproximation

variable {Φ L'} (h : RightApproximation Φ L')

include h in
/-- **Lemma 5.4.2(2).** For a right approximation `t`, if `i ≫ t(f) = j` with
`i, j` weak equivalences, then `f` becomes an isomorphism in `ho M'`. -/
theorem isIso_map {A' C' : M'} (g : A' ⟶ C') {B : M} (i : B ⟶ Φ.functor.obj A')
    (j : B ⟶ Φ.functor.obj C') (hi : W i) (hj : W j) (w : i ≫ Φ.functor.map g = j) :
    IsIso (L'.map g) := by
  have := LeftApproximation.isIso_map h g.op j.op i.op hj hi (by
    change (Φ.functor.map g).op ≫ i.op = j.op
    rw [← op_comp, w])
  exact (isIso_op_iff _).1 this

include h in
/-- **Theorem 5.5.1** (the approximation theorem), for right approximations. -/
theorem isLocalizedEquivalence [W'.IsMultiplicative] [W.IsMultiplicative] :
    Φ.IsLocalizedEquivalence := by
  have := LeftApproximation.isLocalizedEquivalence h
  exact isLocalizedEquivalence_of_op Φ

end RightApproximation

/-- **Corollary 5.5.3(2).** A localizer morphism is a right approximation iff it
satisfies RAP1 and RAP2(1) (that is, LAP1 and LAP2(1) for the opposite localizer
morphism) and induces an equivalence of homotopy categories. -/
theorem rightApproximation_iff [W'.IsMultiplicative] [W.IsMultiplicative] :
    RightApproximation Φ L' ↔
      (∀ A : Mᵒᵖ, ∃ (A' : M'ᵒᵖ) (p : Φ.op.functor.obj A' ⟶ A), W.op p) ∧
      (∀ {A' B' : M'ᵒᵖ} {B : Mᵒᵖ} (f : Φ.op.functor.obj A' ⟶ B) (p : Φ.op.functor.obj B' ⟶ B),
        W.op p → Nonempty (FactorizationData Φ.op f p)) ∧ Φ.IsLocalizedEquivalence := by
  rw [RightApproximation, leftApproximation_iff]
  exact ⟨fun ⟨h₁, h₂, _⟩ ↦ ⟨h₁, h₂, isLocalizedEquivalence_of_op Φ⟩,
    fun ⟨h₁, h₂, _⟩ ↦ ⟨h₁, h₂, inferInstance⟩⟩

section Composition

variable {M'' : Type*} [Category M''] {W'' : MorphismProperty M''} {H'' : Type*} [Category H'']
  (Φ₁ : LocalizerMorphism W'' W') (L'' : M'' ⥤ H'') [L''.IsLocalization W'']
  [W''.IsMultiplicative] [W'.IsMultiplicative] [W.IsMultiplicative]

/-- **Corollary 5.5.4**, left approximations: left approximations are closed
under composition. -/
theorem LeftApproximation.comp (h₁ : LeftApproximation Φ₁ L'') (h₂ : LeftApproximation Φ L') :
    LeftApproximation (Φ₁.comp Φ) L'' := by
  have := h₁.isLocalizedEquivalence
  have := h₂.isLocalizedEquivalence
  rw [leftApproximation_iff]
  refine ⟨fun A ↦ ?_, fun {A'' B'' B} f p hp ↦ ?_, inferInstance⟩
  · obtain ⟨A', p, hp⟩ := h₂.exists_resolution A
    obtain ⟨A'', p', hp'⟩ := h₁.exists_resolution A'
    exact ⟨A'', Φ.functor.map p' ≫ p, W.comp_mem _ _ (Φ.map _ hp') hp⟩
  · obtain ⟨d⟩ := h₂.nonempty_factorizationData f p hp
    obtain ⟨d'⟩ := h₁.nonempty_factorizationData d.i d.j d.hj
    exact ⟨⟨d'.D, d'.i, d'.j, Φ.functor.map d'.σ ≫ d.σ, d'.hj,
      W.comp_mem _ _ (Φ.map _ d'.hσ) d.hσ,
      (show Φ.functor.map (Φ₁.functor.map d'.i) ≫ Φ.functor.map d'.σ ≫ d.σ =
          Φ.functor.map d.i ≫ d.σ by rw [← assoc, ← Φ.functor.map_comp, d'.fac_i]).trans d.fac_i,
      (show Φ.functor.map (Φ₁.functor.map d'.j) ≫ Φ.functor.map d'.σ ≫ d.σ =
          Φ.functor.map d.j ≫ d.σ by rw [← assoc, ← Φ.functor.map_comp, d'.fac_j]).trans d.fac_j⟩⟩

/-- **Corollary 5.5.4**, right approximations: right approximations are closed
under composition. -/
theorem RightApproximation.comp (h₁ : RightApproximation Φ₁ L'')
    (h₂ : RightApproximation Φ L') : RightApproximation (Φ₁.comp Φ) L'' :=
  LeftApproximation.comp Φ.op L'.op Φ₁.op L''.op h₁ h₂

end Composition

end ABCCofibrations

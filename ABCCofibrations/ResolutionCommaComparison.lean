/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionLabelledInsertion
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Equivalence

/-! # The comma comparison of Lemma 9.5.1(1)

For `u : D₁ ⥤ D₂` and `d₂ : D₂`, the paper asserts a natural isomorphism

  (u pₜ ↓ d₂) ≅ Δ′(u ↓ d₂).

We construct the comparison functor

  `resolutionCommaCompare u d₂ : Δ′(u ↓ d₂) ⥤ (u pₜ ↓ d₂)`

which forgets the structure maps of all but the last vertex. We prove that it is
fully faithful and bijective on objects, which is exactly an isomorphism of
categories in the paper's sense. The explicit inverse `resolutionCommaInverse`
composes each vertex's remaining chain with the given arrow `xₙ → d₂`. The
result is packaged as `resolutionCommaEquivalence`. Its counit has identity
components in Δ′D₁, and its unit is given by `eqToIso` of label equalities;
strict functor equalities are avoided.

The inverse-side Lemma 9.5.1(2) is not yet formalized. Δ′ is not invariant
under equivalences of categories (its maps commute with labels strictly), so
the duality route needs a strict isomorphism (d₂ ↓ u)ᵒᵖ ≅ (u.op ↓ op d₂),
not mathlib's equivalence.

The comparison commutes strictly with the projections to Δ′D₁
(`resolutionCommaCompare_proj`).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v₁ v₂ u₁ u₂
open CategoryTheory Limits Opposite
namespace ABCCofibrations

/-! ### Objects of comma categories -/

theorem costructuredArrow_obj_ext {C : Type*} [Category C] {E : Type*} [Category E]
    {S : C ⥤ E} {T : E} {p q : CostructuredArrow S T} (h : p.left = q.left)
    (hh : p.hom = S.map (eqToHom h) ≫ q.hom) : p = q := by
  rcases p with ⟨pl, ⟨⟨⟩⟩, ph⟩
  rcases q with ⟨ql, ⟨⟨⟩⟩, qh⟩
  cases h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp] at hh
  subst hh
  rfl

/-- Functors into a costructured-arrow category agree if their underlying
functors agree and their structure maps correspond. -/
theorem functor_ext_costructuredArrow {J : Type*} [Category J] {C : Type*} [Category C]
    {E : Type*} [Category E] {S : C ⥤ E} {T : E} {F G : J ⥤ CostructuredArrow S T}
    (hleft : F ⋙ CostructuredArrow.proj S T = G ⋙ CostructuredArrow.proj S T)
    (hhom : ∀ j, (F.obj j).hom =
      S.map (eqToHom (Functor.congr_obj hleft j)) ≫ (G.obj j).hom) : F = G :=
  CategoryTheory.Functor.ext (fun j ↦ costructuredArrow_obj_ext _ (hhom j))
    (fun i j f ↦ by
      apply CostructuredArrow.hom_ext
      simp only [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
      exact Functor.congr_hom hleft f)

/-! ### Lifting a labelled chain into the comma category -/

section Lift

variable {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂} [Category.{v₂} D₂]
  (u : D₁ ⥤ D₂) (d₂ : D₂)

/-- A chain `x₀ → ⋯ → xₙ` together with `a : u xₙ ⟶ d₂` becomes a chain in
`u ↓ d₂`, whose `i`-th structure map is `u(xᵢ → xₙ) ≫ a`. -/
def chainToComma {n : ℕ} (X : Fin (n + 1) ⥤ D₁) (a : u.obj (X.obj (Fin.last n)) ⟶ d₂) :
    Fin (n + 1) ⥤ CostructuredArrow u d₂ :=
  X.toCostructuredArrow u d₂ (fun i ↦ u.map (X.map (homOfLE (Fin.le_last i))) ≫ a)
    (fun {i j} g ↦ by
      rw [← Category.assoc, ← u.map_comp, ← X.map_comp]
      rfl)

@[simp] theorem chainToComma_proj {n : ℕ} (X : Fin (n + 1) ⥤ D₁)
    (a : u.obj (X.obj (Fin.last n)) ⟶ d₂) :
    chainToComma u d₂ X a ⋙ CostructuredArrow.proj u d₂ = X :=
  rfl

/-- Reindexing a lifted chain lifts the reindexed chain. -/
theorem comp_chainToComma {n m : ℕ} (F : Fin (n + 1) ⥤ Fin (m + 1)) (Y : Fin (m + 1) ⥤ D₁)
    (b : u.obj (Y.obj (Fin.last m)) ⟶ d₂) :
    F ⋙ chainToComma u d₂ Y b =
      chainToComma u d₂ (F ⋙ Y)
        (u.map (Y.map (homOfLE (Fin.le_last (F.obj (Fin.last n))))) ≫ b) :=
  functor_ext_costructuredArrow rfl (fun j ↦ by
    simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
    change u.map (Y.map _) ≫ b = u.map (Y.map (F.map _)) ≫ u.map (Y.map _) ≫ b
    rw [← Category.assoc, ← u.map_comp, ← Y.map_comp]
    rfl)

theorem chainToComma_congr {n : ℕ} {X X' : Fin (n + 1) ⥤ D₁} (h : X = X')
    {a : u.obj (X.obj (Fin.last n)) ⟶ d₂} {a' : u.obj (X'.obj (Fin.last n)) ⟶ d₂}
    (ha : a = u.map (eqToHom (by rw [h])) ≫ a') :
    chainToComma u d₂ X a = chainToComma u d₂ X' a' := by
  subst h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp] at ha
  subst ha
  rfl

end Lift

/-! ### The comparison functor -/

section Comparison

variable {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂} [Category.{v₂} D₂]
  (u : D₁ ⥤ D₂) (d₂ : D₂)

theorem resolutionTerminal_map_resolutionMap {E : Type*} [Category E] (F : D₁ ⥤ E)
    {x y : SemisimplicialResolution D₁} (f : x ⟶ y) :
    (resolutionTerminal E).map ((resolutionMap F).map f) =
      F.map ((resolutionTerminal D₁).map f) := by
  simpa using Functor.congr_hom (resolutionMap_terminal F) f

/-- The comparison Δ′(u ↓ d₂) ⥤ (u pₜ ↓ d₂) of Lemma 9.5.1(1): keep the
underlying chain in D₁ and the structure map of its last vertex. -/
def resolutionCommaCompare :
    SemisimplicialResolution (CostructuredArrow u d₂) ⥤
      CostructuredArrow (resolutionTerminal D₁ ⋙ u) d₂ :=
  (resolutionMap (CostructuredArrow.proj u d₂)).toCostructuredArrow
    (resolutionTerminal D₁ ⋙ u) d₂
    (fun c ↦ ((resolutionTerminal (CostructuredArrow u d₂)).obj c).hom)
    (fun {c c'} g ↦ by
      change u.map ((resolutionTerminal D₁).map
        ((resolutionMap (CostructuredArrow.proj u d₂)).map g)) ≫ _ = _
      rw [resolutionTerminal_map_resolutionMap]
      exact CostructuredArrow.w ((resolutionTerminal (CostructuredArrow u d₂)).map g))

/-- The comparison commutes strictly with the projections to Δ′D₁. -/
theorem resolutionCommaCompare_proj :
    resolutionCommaCompare u d₂ ⋙ CostructuredArrow.proj _ _ =
      resolutionMap (CostructuredArrow.proj u d₂) :=
  rfl

/-- The labels in `u ↓ d₂` attached to an object of (u pₜ ↓ d₂). -/
def resolutionCommaLabel (p : CostructuredArrow (resolutionTerminal D₁ ⋙ u) d₂) :
    Fin (p.left.unop.obj.unop.len + 1) ⥤ CostructuredArrow u d₂ :=
  chainToComma u d₂ (resolutionLabel p.left) p.hom

/-- The inverse of the comparison on objects. -/
def resolutionCommaLift (p : CostructuredArrow (resolutionTerminal D₁ ⋙ u) d₂) :
    SemisimplicialResolution (CostructuredArrow u d₂) :=
  op ((semisimplicialNerve _).elementsMk p.left.unop.obj (resolutionCommaLabel u d₂ p))

theorem resolutionCommaLabel_compare (c : SemisimplicialResolution (CostructuredArrow u d₂)) :
    resolutionCommaLabel u d₂ ((resolutionCommaCompare u d₂).obj c) = resolutionLabel c :=
  functor_ext_costructuredArrow rfl (fun j ↦ by
    simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
    exact CostructuredArrow.w ((resolutionLabel c).map (homOfLE (Fin.le_last j))))

theorem resolutionCommaLift_compare (c : SemisimplicialResolution (CostructuredArrow u d₂)) :
    resolutionCommaLift u d₂ ((resolutionCommaCompare u d₂).obj c) = c := by
  change op ((semisimplicialNerve _).elementsMk c.unop.obj
    (resolutionCommaLabel u d₂ ((resolutionCommaCompare u d₂).obj c))) = c
  rw [resolutionCommaLabel_compare]

theorem resolutionCommaCompare_lift (p : CostructuredArrow (resolutionTerminal D₁ ⋙ u) d₂) :
    (resolutionCommaCompare u d₂).obj (resolutionCommaLift u d₂ p) = p :=
  costructuredArrow_obj_ext rfl (by
    simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
    change u.map ((resolutionLabel p.left).map (homOfLE (Fin.le_last _))) ≫ p.hom = p.hom
    rw [show homOfLE (Fin.le_last (Fin.last p.left.unop.obj.unop.len)) = 𝟙 _ from
      Subsingleton.elim _ _]
    simp)

theorem resolutionCommaCompare_lift_hom
    (p : CostructuredArrow (resolutionTerminal D₁ ⋙ u) d₂) :
    ((resolutionCommaCompare u d₂).obj (resolutionCommaLift u d₂ p)).hom = p.hom := by
  change u.map ((resolutionLabel p.left).map (homOfLE (Fin.le_last _))) ≫ p.hom = p.hom
  rw [show homOfLE (Fin.le_last (Fin.last p.left.unop.obj.unop.len)) = 𝟙 _ from
    Subsingleton.elim _ _]
  simp

/-- The comparison is a bijection on objects. -/
theorem resolutionCommaCompare_obj_bijective :
    Function.Bijective (resolutionCommaCompare u d₂).obj :=
  ⟨Function.LeftInverse.injective (resolutionCommaLift_compare u d₂),
    Function.RightInverse.surjective (resolutionCommaCompare_lift u d₂)⟩

/-- Labels lifted along a morphism of (u pₜ ↓ d₂) are compatible. -/
theorem resolutionCommaLabel_map {p q : CostructuredArrow (resolutionTerminal D₁ ⋙ u) d₂}
    (g : p ⟶ q) :
    (semisimplicialNerve (CostructuredArrow u d₂)).map g.left.unop.hom
      (resolutionCommaLabel u d₂ q) = resolutionCommaLabel u d₂ p := by
  change _ ⋙ chainToComma u d₂ (resolutionLabel q.left) q.hom = _
  rw [comp_chainToComma]
  refine chainToComma_congr u d₂ g.left.unop.map_val ?_
  rw [← CostructuredArrow.w g]
  simp [resolutionTerminal, resolutionTerminalMap, resolutionTerminalObject]

instance : (resolutionCommaCompare u d₂).Faithful where
  map_injective {c c'} f g h := by
    have h' := congrArg CommaMorphism.left h
    exact resolution_hom_ext (congrArg (resolutionOrdinal D₁).map h')

instance : (resolutionCommaCompare u d₂).Full where
  map_surjective {c c'} g := by
    refine ⟨Quiver.Hom.op ⟨g.left.unop.hom, ?_⟩, ?_⟩
    · have h := resolutionCommaLabel_map u d₂ g
      rw [resolutionCommaLabel_compare, resolutionCommaLabel_compare] at h
      exact h
    · exact CostructuredArrow.hom_ext _ _ (resolution_hom_ext rfl)

instance : (resolutionCommaCompare u d₂).EssSurj where
  mem_essImage p := ⟨resolutionCommaLift u d₂ p, ⟨eqToIso (resolutionCommaCompare_lift u d₂ p)⟩⟩

instance : (resolutionCommaCompare u d₂).IsEquivalence where

/-- The explicit inverse of the comparison, on objects `resolutionCommaLift`. -/
def resolutionCommaInverse :
    CostructuredArrow (resolutionTerminal D₁ ⋙ u) d₂ ⥤
      SemisimplicialResolution (CostructuredArrow u d₂) where
  obj := resolutionCommaLift u d₂
  map g := Quiver.Hom.op ⟨g.left.unop.hom, resolutionCommaLabel_map u d₂ g⟩
  map_id _ := resolution_hom_ext rfl
  map_comp _ _ := resolution_hom_ext rfl

/-- The inverse followed by the comparison is the identity, up to an isomorphism
whose underlying map in Δ′D₁ is an identity. -/
def resolutionCommaCounitIso :
    resolutionCommaInverse u d₂ ⋙ resolutionCommaCompare u d₂ ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun p ↦ CostructuredArrow.isoMk (Iso.refl _) (by
      simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]
      exact (resolutionCommaCompare_lift_hom u d₂ p).symm))
    (fun g ↦ CostructuredArrow.hom_ext _ _ (by
      simp only [Functor.comp_map, CostructuredArrow.comp_left, Functor.id_map]
      exact (Category.comp_id _).trans ((resolution_hom_ext rfl).trans
        (Category.id_comp _).symm)))

/-- The comparison followed by the inverse is the identity, up to an isomorphism
whose underlying ordinal map is an identity. -/
def resolutionCommaUnitIso :
    𝟭 _ ≅ resolutionCommaCompare u d₂ ⋙ resolutionCommaInverse u d₂ :=
  NatIso.ofComponents (fun c ↦ eqToIso (resolutionCommaLift_compare u d₂ c).symm)
    (fun {c c'} f ↦ by
      apply resolution_hom_ext
      simp only [Functor.id_map, Functor.map_comp, eqToIso.hom, eqToHom_map]
      have h1 := congrArg (fun x ↦ x.unop.obj.unop) (resolutionCommaLift_compare u d₂ c)
      have h2 := congrArg (fun x ↦ x.unop.obj.unop) (resolutionCommaLift_compare u d₂ c')
      rw [eqToHom_refl _ h1.symm, eqToHom_refl _ h2.symm]
      exact (Category.comp_id _).trans ((Category.id_comp _).symm))

/-- Lemma 9.5.1(1): Δ′(u ↓ d₂) ≌ (u pₜ ↓ d₂), with explicit inverse. -/
def resolutionCommaEquivalence :
    SemisimplicialResolution (CostructuredArrow u d₂) ≌
      CostructuredArrow (resolutionTerminal D₁ ⋙ u) d₂ :=
  CategoryTheory.Equivalence.mk (resolutionCommaCompare u d₂) (resolutionCommaInverse u d₂)
    (resolutionCommaUnitIso u d₂) (resolutionCommaCounitIso u d₂)

end Comparison

end ABCCofibrations

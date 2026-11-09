/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Extension
public import ABCCofibrations.HomotopyCategory

/-!
# Cancellation of weak equivalences up to left homotopy

Postcomposition and precomposition by a weak equivalence between cofibrant
objects reflect left homotopy (Theorem 6.4.3(1)(b)). Postcomposition uses a
pushout of the cylinder boundary and CF4. Precomposition extends that cylinder
along the weak equivalence and cancels the resulting trivial cofibration.

The postcomposition reflection argument also works with an arbitrary ambient
codomain. In particular, equality after an ambient weak equivalence implies
left homotopy, as in Lemma 6.1.3(1) for inclusion of cofibrant objects.
-/

public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {A B : C} [IsCofibrant A] [IsCofibrant B] [HasBinaryCoproduct A A]

namespace LeftHomotopyRel

/-- Strict homotopy after an ambient weak equivalence implies left homotopy.
The codomain of the weak equivalence need not be cofibrant. -/
theorem of_postcomp_weakEquivalence_of_strict {f g : A ⟶ B}
    {D : C} (b : B ⟶ D) [WeakEquivalence b]
    (h : StrictLeftHomotopyRel (f ≫ b) (g ≫ b)) : LeftHomotopyRel f g := by
  obtain ⟨P, hP, ⟨H⟩⟩ := h
  let := hP
  let := coprod_cofibrant (A := A) (B := A)
  let := cylinder_cofibrant P
  let d := coprod.desc f g
  let sq := IsPushout.of_hasPushout P.i d
  let := cofibration_of_isPushout sq
  let := cofibrant_target (pushout.inr P.i d)
  have hboundary : P.i ≫ H.h = d ≫ b := by
    ext <;> simp [Precylinder.i, d, H.h₀, H.h₁]
  let u := pushout.desc H.h b hboundary
  obtain ⟨Z, j, p, hj, hp, hjp⟩ := factorization u
  let := hj
  let := hp
  let q := pushout.inr P.i d ≫ j
  have hqp : q ≫ p = b := by
    dsimp [q]
    rw [Category.assoc, hjp]
    exact pushout.inr_desc _ _ _
  have hq : Cofibration q := by dsimp [q]; infer_instance
  have hqw : WeakEquivalence q := weakEquivalence_of_postcomp_of_fac hqp
  refine ⟨Z, q, hq, hqw, P, hP, ⟨?_⟩⟩
  exact
    { h := pushout.inl P.i d ≫ j
      h₀ := by
        have he := congrArg (fun k ↦ coprod.inl ≫ k) sq.w
        simp only [Precylinder.inl_i_assoc] at he
        dsimp [d] at he
        simpa [q, Category.assoc] using congrArg (fun k ↦ k ≫ j) he
      h₁ := by
        have he := congrArg (fun k ↦ coprod.inr ≫ k) sq.w
        simp only [Precylinder.inr_i_assoc] at he
        dsimp [d] at he
        simpa [q, Category.assoc] using congrArg (fun k ↦ k ≫ j) he }

/-- A weak equivalence after the target can be cancelled from a left homotopy,
even when its codomain is not cofibrant. -/
theorem of_postcomp_weakEquivalence {f g : A ⟶ B}
    {D : C} (b : B ⟶ D) [WeakEquivalence b]
    (h : LeftHomotopyRel (f ≫ b) (g ≫ b)) : LeftHomotopyRel f g := by
  obtain ⟨E, c, _, hcw, h⟩ := h
  let := hcw
  exact of_postcomp_weakEquivalence_of_strict (b ≫ c)
    (by simpa only [Category.assoc] using h)

/-- Equality after an ambient weak equivalence implies left homotopy.
This is Lemma 6.1.3(1) for the inclusion of cofibrant objects. -/
theorem of_postcomp_weakEquivalence_eq {f g : A ⟶ B}
    {D : C} (b : B ⟶ D) [WeakEquivalence b]
    (h : f ≫ b = g ≫ b) : LeftHomotopyRel f g := by
  apply of_postcomp_weakEquivalence_of_strict b
  rw [h]
  exact StrictLeftHomotopyRel.refl _

/-- Postcomposition by a weak equivalence preserves and reflects left homotopy. -/
theorem postcomp_weakEquivalence_iff {f g : A ⟶ B}
    {D : C} [IsCofibrant D] (b : B ⟶ D) [WeakEquivalence b] :
    LeftHomotopyRel (f ≫ b) (g ≫ b) ↔ LeftHomotopyRel f g :=
  ⟨of_postcomp_weakEquivalence b, fun h ↦ h.postcomp b⟩

/-- A weak equivalence before the source can be cancelled from a left homotopy
(Theorem 6.4.3(1)(b)(i)). -/
theorem of_precomp_weakEquivalence {A' : C} [IsCofibrant A']
    [HasBinaryCoproduct A' A'] (a : A' ⟶ A) [WeakEquivalence a] {f g : A ⟶ B}
    (h : LeftHomotopyRel (a ≫ f) (a ≫ g)) : LeftHomotopyRel f g := by
  obtain ⟨P, hP⟩ := exists_good_cylinder A'
  let := hP
  let := coprod_cofibrant (A := A') (B := A')
  let := coprod_cofibrant (A := A) (B := A)
  let := weakEquivalence_coprod_map_of_weakEquivalence a a
  obtain ⟨Q, c, k, hQ, _, hk, _, _, hπ, hkinl, hkinr⟩ :=
    exists_relative_good_cylinder P a
  let := hQ
  let := hk
  obtain ⟨B'', b'', hb'', hbw, ⟨H⟩⟩ := h.exists_on_cylinder P
  let := hb''
  let := hbw
  let := cofibrant_target b''
  have hsq : P.i ≫ H.h =
      coprod.map a a ≫ coprod.desc (f ≫ b'') (g ≫ b'') := by
    ext <;> simp [Precylinder.i, H.h₀, H.h₁]
  let u := pushout.desc H.h (coprod.desc (f ≫ b'') (g ≫ b'')) hsq
  let := weakEquivalence_pushout_inl P.i (coprod.map a a)
  have hc : WeakEquivalence c :=
    weakEquivalence_of_postcomp_of_fac (g := Q.π) (fg := P.π ≫ a) hπ
  let := hc
  have hkw : WeakEquivalence k :=
    weakEquivalence_of_precomp_of_fac (f := pushout.inl P.i (coprod.map a a)) hkinl
  let := hkw
  let := cofibration_of_isPushout (IsPushout.of_hasPushout P.i (coprod.map a a))
  let := cofibrant_target (pushout.inr P.i (coprod.map a a))
  let b' := pushout.inr k u
  have hb' : Cofibration b' :=
    cofibration_of_isPushout (IsPushout.of_hasPushout k u)
  have hb'w : WeakEquivalence b' :=
    weakEquivalence_of_isPushout (IsPushout.of_hasPushout k u)
  let := hb'
  let := hb'w
  let := cofibrant_target b'
  have hhom : LeftHomotopyRel (f ≫ b'' ≫ b') (g ≫ b'' ≫ b') := by
    refine of_strict ⟨Q, hQ, ⟨?_⟩⟩
    exact
      { h := pushout.inl k u
        h₀ := by
          rw [← Precylinder.inl_i (P := Q.toPrecylinder), ← hkinr, Category.assoc,
            Category.assoc,
            pushout.condition,
            ← Category.assoc (pushout.inr P.i (coprod.map a a)) u b',
            pushout.inr_desc, ← Category.assoc, coprod.inl_desc, Category.assoc]
        h₁ := by
          rw [← Precylinder.inr_i (P := Q.toPrecylinder), ← hkinr, Category.assoc,
            Category.assoc,
            pushout.condition,
            ← Category.assoc (pushout.inr P.i (coprod.map a a)) u b',
            pushout.inr_desc, ← Category.assoc, coprod.inr_desc, Category.assoc] }
  exact of_postcomp_weakEquivalence (b'' ≫ b') hhom

/-- Precomposition by a weak equivalence preserves and reflects left homotopy. -/
theorem precomp_weakEquivalence_iff {A' : C} [IsCofibrant A']
    [HasBinaryCoproduct A' A'] (a : A' ⟶ A) [WeakEquivalence a] {f g : A ⟶ B} :
    LeftHomotopyRel (a ≫ f) (a ≫ g) ↔ LeftHomotopyRel f g :=
  ⟨of_precomp_weakEquivalence a, fun h ↦ h.precomp a⟩

end LeftHomotopyRel

/-- Weak equivalences act as monomorphisms on left-homotopy classes. -/
theorem mono_toLeftHomotopyCategory_map
    {X Y : CofibrantObject C} (f : X ⟶ Y) [WeakEquivalence f.hom] :
    Mono ((toLeftHomotopyCategory (C := C)).map f) := by
  constructor
  rintro ⟨Z⟩ ⟨g⟩ ⟨h⟩ he
  change Z ⟶ X at g h
  apply (toLeftHomotopyCategory_map_eq_iff g h).2
  have hh : cofibrantLeftHomotopyRel (g ≫ f) (h ≫ f) := by
    apply (toLeftHomotopyCategory_map_eq_iff _ _).1
    change toLeftHomotopyCategory.map g ≫ toLeftHomotopyCategory.map f =
      toLeftHomotopyCategory.map h ≫ toLeftHomotopyCategory.map f at he
    rw [← Functor.map_comp, ← Functor.map_comp] at he
    exact he
  let := hasBinaryCoproduct Z.obj Z.obj
  change LeftHomotopyRel g.hom h.hom
  exact LeftHomotopyRel.of_postcomp_weakEquivalence
    (f := g.hom) (g := h.hom) f.hom hh

/-- Every weak equivalence in the homotopy quotient is a monomorphism. -/
instance mono_of_weakEquivalence_leftHomotopyCategory
    {X Y : LeftHomotopyCategory C} (f : X ⟶ Y) [WeakEquivalence f] : Mono f := by
  have hw := ‹WeakEquivalence f›
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  rcases f with ⟨f⟩
  change X ⟶ Y at f
  change WeakEquivalence ((toLeftHomotopyCategory (C := C)).map f) at hw
  let := (weakEquivalence_toLeftHomotopyCategory_map_iff f).1 hw
  exact mono_toLeftHomotopyCategory_map f

end ABCCofibrations.ABCPrecofibrationCategory

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.HomotopyCategory

/-!
# Cancellation of weak equivalences up to left homotopy

Postcomposition by a weak equivalence between cofibrant objects reflects
left homotopy (Theorem 6.4.3(1)(b)(ii)). The proof uses a pushout of the
cylinder boundary and CF4, without a calculus of fractions or localization.
-/

public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {A B : C} [IsCofibrant A] [IsCofibrant B] [HasBinaryCoproduct A A]

namespace LeftHomotopyRel

/-- A weak equivalence after the target can be cancelled from a left homotopy. -/
theorem of_postcomp_weakEquivalence {f g : A ⟶ B}
    {D : C} [IsCofibrant D] (b : B ⟶ D) [WeakEquivalence b]
    (h : LeftHomotopyRel (f ≫ b) (g ≫ b)) : LeftHomotopyRel f g := by
  obtain ⟨E, c, hc, hcw, P, hP, ⟨H⟩⟩ := h
  let := hP
  let := hcw
  let := coprod_cofibrant (A := A) (B := A)
  let := cylinder_cofibrant P
  let d := coprod.desc f g
  let sq := IsPushout.of_hasPushout P.i d
  let := cofibration_of_isPushout sq
  let := cofibrant_target (pushout.inr P.i d)
  have hboundary : P.i ≫ H.h = d ≫ (b ≫ c) := by
    ext <;> simp [Precylinder.i, d, H.h₀, H.h₁, Category.assoc]
  let u := pushout.desc H.h (b ≫ c) hboundary
  obtain ⟨Z, j, p, hj, hp, hjp⟩ := factorization u
  let := hj
  let := hp
  let q := pushout.inr P.i d ≫ j
  have hqp : q ≫ p = b ≫ c := by
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

/-- Postcomposition by a weak equivalence preserves and reflects left homotopy. -/
theorem postcomp_weakEquivalence_iff {f g : A ⟶ B}
    {D : C} [IsCofibrant D] (b : B ⟶ D) [WeakEquivalence b] :
    LeftHomotopyRel (f ≫ b) (g ≫ b) ↔ LeftHomotopyRel f g :=
  ⟨of_postcomp_weakEquivalence b, fun h ↦ h.postcomp b⟩

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

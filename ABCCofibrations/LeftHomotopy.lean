/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Cylinder
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy

/-!
# Strict left homotopy and left homotopy

Following §6.3 of Rădulescu-Banu, *Cofibrations in Homotopy Theory*, strict
homotopy uses a good cylinder directly, while left homotopy allows a trivial
cofibration of the target. The homotopy data are mathlib's
`Cylinder.LeftHomotopy`. No model-category axioms are assumed.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {A B : C} [IsCofibrant A] [HasBinaryCoproduct A A]

/-- Strict left homotopy through some good cylinder, without changing the target. -/
def StrictLeftHomotopyRel (f g : A ⟶ B) : Prop :=
  ∃ P : Cylinder A, P.IsGood ∧ Nonempty (P.LeftHomotopy f g)

namespace StrictLeftHomotopyRel

/-- Constant homotopies give reflexivity. -/
theorem refl (f : A ⟶ B) : StrictLeftHomotopyRel f f := by
  obtain ⟨P, hP⟩ := exists_good_cylinder A
  exact ⟨P, hP, ⟨Cylinder.LeftHomotopy.refl P f⟩⟩

/-- Reversing a cylinder reverses the homotopy. -/
theorem symm {f g : A ⟶ B} (h : StrictLeftHomotopyRel f g) :
    StrictLeftHomotopyRel g f := by
  obtain ⟨P, hP, ⟨H⟩⟩ := h
  let := hP
  exact ⟨P.symm, good_cylinder_symm P, ⟨H.symm⟩⟩

/-- Concatenating good cylinders composes strict homotopies. -/
theorem trans {f g h : A ⟶ B} (hfg : StrictLeftHomotopyRel f g)
    (hgh : StrictLeftHomotopyRel g h) : StrictLeftHomotopyRel f h := by
  obtain ⟨P, hP, ⟨H⟩⟩ := hfg
  obtain ⟨Q, hQ, ⟨K⟩⟩ := hgh
  let := hP
  let := hQ
  let := cylinder_cofibrant Q
  let := cofibration_cylinder_i₁ P
  exact ⟨cylinder_trans P Q, good_cylinder_trans P Q,
    ⟨Precylinder.LeftHomotopy.trans H K⟩⟩

omit [HasInitial C] [ABCPrecofibrationCategory C] [IsCofibrant A] in
/-- Strict homotopies can be postcomposed with any morphism. -/
theorem postcomp {f g : A ⟶ B} (h : StrictLeftHomotopyRel f g)
    {D : C} (k : B ⟶ D) : StrictLeftHomotopyRel (f ≫ k) (g ≫ k) := by
  obtain ⟨P, hP, ⟨H⟩⟩ := h
  exact ⟨P, hP, ⟨H.postcomp k⟩⟩

/-- Strict left homotopy is an equivalence relation. -/
theorem equivalence : Equivalence (StrictLeftHomotopyRel (A := A) (B := B)) :=
  ⟨refl, symm, trans⟩

omit [HasInitial C] [ABCPrecofibrationCategory C] [IsCofibrant A] in
/-- Forgetting goodness gives mathlib's unrestricted cylinder homotopy relation. -/
theorem to_mathlib {f g : A ⟶ B} (h : StrictLeftHomotopyRel f g) :
    HomotopicalAlgebra.LeftHomotopyRel f g := by
  obtain ⟨P, _, H⟩ := h
  exact ⟨P, H⟩

omit [IsCofibrant A] in
/-- Strictly homotopic maps are weak equivalences simultaneously. -/
theorem weakEquivalence_iff {f g : A ⟶ B} (h : StrictLeftHomotopyRel f g) :
    WeakEquivalence f ↔ WeakEquivalence g := by
  obtain ⟨P, _, ⟨H⟩⟩ := h
  let : (weakEquivalences C).ContainsIdentities :=
    ⟨fun X ↦ (weakEquivalence_of_isIso (𝟙 X)).mem⟩
  exact H.weakEquivalence_iff

end StrictLeftHomotopyRel

/-- Left homotopy in the sense of §6.3: strict homotopy after a trivial
cofibration of the target. -/
def LeftHomotopyRel (f g : A ⟶ B) : Prop :=
  ∃ (B' : C) (b : B ⟶ B'), Cofibration b ∧ WeakEquivalence b ∧
    StrictLeftHomotopyRel (f ≫ b) (g ≫ b)

namespace LeftHomotopyRel

variable [IsCofibrant B]

omit [IsCofibrant A] in
/-- A strict homotopy gives a left homotopy using the identity target map. -/
theorem of_strict {f g : A ⟶ B} (h : StrictLeftHomotopyRel f g) :
    LeftHomotopyRel f g := by
  refine ⟨B, 𝟙 B, cofibration_of_isIso _, weakEquivalence_of_isIso _, ?_⟩
  simpa using h

/-- Left homotopy is reflexive on maps between cofibrant objects. -/
theorem refl (f : A ⟶ B) : LeftHomotopyRel f f := of_strict (.refl f)

omit [IsCofibrant B] in
/-- Left homotopy is symmetric. -/
theorem symm {f g : A ⟶ B} (h : LeftHomotopyRel f g) : LeftHomotopyRel g f := by
  obtain ⟨B', b, hb, hw, H⟩ := h
  exact ⟨B', b, hb, hw, H.symm⟩

/-- A common target pushout lets us concatenate left homotopies. -/
theorem trans {f g h : A ⟶ B} (hfg : LeftHomotopyRel f g)
    (hgh : LeftHomotopyRel g h) : LeftHomotopyRel f h := by
  obtain ⟨D, b, hb, hbw, H⟩ := hfg
  obtain ⟨E, c, hc, hcw, K⟩ := hgh
  let := hb
  let := hbw
  let := hc
  let := hcw
  let := cofibrant_target b
  let := cofibrant_target c
  let := cofibration_of_isPushout (IsPushout.of_hasPushout b c).flip
  let := weakEquivalence_of_isPushout (IsPushout.of_hasPushout b c).flip
  have hi : Cofibration (b ≫ pushout.inl b c) := inferInstance
  have hw : WeakEquivalence (b ≫ pushout.inl b c) := inferInstance
  refine ⟨pushout b c, b ≫ pushout.inl b c, hi, hw, ?_⟩
  have H' := H.postcomp (pushout.inl b c)
  have K' := K.postcomp (pushout.inr b c)
  have H'' : StrictLeftHomotopyRel (f ≫ b ≫ pushout.inl b c)
      (g ≫ b ≫ pushout.inl b c) := by simpa only [Category.assoc] using H'
  have K'' : StrictLeftHomotopyRel (g ≫ b ≫ pushout.inl b c)
      (h ≫ b ≫ pushout.inl b c) := by
    simpa only [Category.assoc, pushout.condition] using K'
  exact H''.trans K''

omit [IsCofibrant A] in
/-- Postcomposition transports a homotopy by pushing out its target enlargement. -/
theorem postcomp {f g : A ⟶ B} (h : LeftHomotopyRel f g)
    {D : C} [IsCofibrant D] (k : B ⟶ D) :
    LeftHomotopyRel (f ≫ k) (g ≫ k) := by
  obtain ⟨B', b, hb, hw, H⟩ := h
  let := hb
  let := hw
  have hj : Cofibration (pushout.inr b k) :=
    cofibration_of_isPushout (IsPushout.of_hasPushout b k)
  have hjw : WeakEquivalence (pushout.inr b k) :=
    weakEquivalence_of_isPushout (IsPushout.of_hasPushout b k)
  refine ⟨pushout b k, pushout.inr b k, hj, hjw, ?_⟩
  simpa only [Category.assoc, pushout.condition] using H.postcomp (pushout.inl b k)

/-- A left homotopy can be represented on any given good cylinder
(Lemma 6.3.2(1)), after enlarging the target by a trivial cofibration. -/
theorem exists_on_cylinder {f g : A ⟶ B} (h : LeftHomotopyRel f g)
    (Q : Cylinder A) [Q.IsGood] :
    ∃ (B' : C) (b : B ⟶ B'), Cofibration b ∧ WeakEquivalence b ∧
      Nonempty (Q.LeftHomotopy (f ≫ b) (g ≫ b)) := by
  obtain ⟨D, b, hb, hbw, P, hP, ⟨H⟩⟩ := h
  let := hb
  let := hbw
  let := hP
  let := cofibrant_target b
  let := coprod_cofibrant (A := A) (B := A)
  let := cylinder_cofibrant P
  let := cylinder_cofibrant Q
  obtain ⟨R, j, k, _, hj, hjw, _, _, hP₀, hP₁, _, hQ₀, hQ₁, _⟩ :=
    exists_common_cylinder_refinement P Q
  let := hj
  let := hjw
  let := cofibration_of_isPushout (IsPushout.of_hasPushout j H.h)
  let := weakEquivalence_of_isPushout (IsPushout.of_hasPushout j H.h)
  have hcof : Cofibration (b ≫ pushout.inr j H.h) := inferInstance
  have hwe : WeakEquivalence (b ≫ pushout.inr j H.h) := inferInstance
  refine ⟨pushout j H.h, b ≫ pushout.inr j H.h, hcof, hwe, ⟨?_⟩⟩
  exact
    { h := k ≫ pushout.inl j H.h
      h₀ := by
        rw [← Category.assoc, hQ₀, ← hP₀, Category.assoc, pushout.condition,
          ← Category.assoc, H.h₀, Category.assoc]
      h₁ := by
        rw [← Category.assoc, hQ₁, ← hP₁, Category.assoc, pushout.condition,
          ← Category.assoc, H.h₁, Category.assoc] }

/-- Relative cylinders and change of cylinder make left homotopy compatible
with precomposition by a map from a cofibrant object (Theorem 6.3.3(1)(b)). -/
theorem precomp {f g : A ⟶ B} (h : LeftHomotopyRel f g)
    {D : C} [IsCofibrant D] [HasBinaryCoproduct D D] (k : D ⟶ A) :
    LeftHomotopyRel (k ≫ f) (k ≫ g) := by
  obtain ⟨P, hP⟩ := exists_good_cylinder D
  let := hP
  let := coprod_cofibrant (A := D) (B := D)
  let := coprod_cofibrant (A := A) (B := A)
  obtain ⟨Q, c, _, hQ, _, _, h₀, h₁, _, _, _⟩ :=
    exists_relative_good_cylinder P k
  let := hQ
  obtain ⟨B', b, hb, hw, ⟨H⟩⟩ := h.exists_on_cylinder Q
  refine ⟨B', b, hb, hw, P, hP, ⟨?_⟩⟩
  exact
    { h := c ≫ H.h
      h₀ := by rw [← Category.assoc, h₀, Category.assoc, H.h₀, ← Category.assoc]
      h₁ := by rw [← Category.assoc, h₁, Category.assoc, H.h₁, ← Category.assoc] }

/-- Two left homotopies can be composed horizontally. -/
theorem comp {D : C} [IsCofibrant D] [HasBinaryCoproduct B B]
    {f g : A ⟶ B} {k l : B ⟶ D}
    (hfg : LeftHomotopyRel f g) (hkl : LeftHomotopyRel k l) :
    LeftHomotopyRel (f ≫ k) (g ≫ l) :=
  (hfg.postcomp k).trans (hkl.precomp g)

/-- Left homotopy is an equivalence relation on maps between cofibrant objects. -/
theorem equivalence : Equivalence (LeftHomotopyRel (A := A) (B := B)) :=
  ⟨refl, symm, trans⟩

omit [IsCofibrant A] [IsCofibrant B] in
/-- Weak equivalence is invariant under the paper's left-homotopy relation. -/
theorem weakEquivalence_iff {f g : A ⟶ B} (h : LeftHomotopyRel f g) :
    WeakEquivalence f ↔ WeakEquivalence g := by
  obtain ⟨B', b, _, hw, H⟩ := h
  let := hw
  exact (weakEquivalence_postcomp_iff f b).symm.trans
    (H.weakEquivalence_iff.trans (weakEquivalence_postcomp_iff g b))

end LeftHomotopyRel

end ABCCofibrations.ABCPrecofibrationCategory

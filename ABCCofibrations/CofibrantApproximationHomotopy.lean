/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.CofibrantApproximation
public import ABCCofibrations.HomotopyLocalization

/-!
# Homotopy cancellation and fraction independence for cofibrant approximations

Lemma 6.1.2(1): equality after an ambient weak equivalence implies left
homotopy in the source of a cofibrant approximation. The proof factors the
full boundary first, so CFA3 is used only on a pushout of two cofibrations.
Lemma 6.1.3(1) follows using common resolutions and cancellation, without
first replacing weak-equivalence denominators by trivial cofibrations.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.IsCofibrantApproximation

open ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] [HasInitial D] [ABCPrecofibrationCategory D]
  (F : C ⥤ D) [IsCofibrantApproximation F]

/-- Maps from the image of a source coproduct are determined by their
restrictions to the images of its two inclusions. -/
theorem map_coprod_hom_ext {A B : C} [HasBinaryCoproduct A B]
    {X : D} {f g : F.obj (A ⨿ B) ⟶ X}
    (h₀ : F.map coprod.inl ≫ f = F.map coprod.inl ≫ g)
    (h₁ : F.map coprod.inr ≫ f = F.map coprod.inr ≫ g) : f = g := by
  let (A : C) : IsCofibrant A := source_cofibrant F A
  exact (map_isPushout (F := F) (IsPushout.of_hasBinaryCoproduct' A B)).hom_ext h₀ h₁

/-- The cancellation construction when the full boundary map is already a
cofibration. This restriction is what permits the use of CFA3. -/
theorem leftHomotopy_of_map_postcomp_eq_of_cofibration
    {A B : C} [HasBinaryCoproduct A A] (f g : A ⟶ B)
    [Cofibration (coprod.desc f g)] {X : D}
    (b : F.obj B ⟶ X) [WeakEquivalence b]
    (h : F.map f ≫ b = F.map g ≫ b) : ABCPrecofibrationCategory.LeftHomotopyRel f g := by
  let (A : C) : IsCofibrant A := source_cofibrant F A
  obtain ⟨P, hP⟩ := exists_good_cylinder A
  let := hP
  let d := coprod.desc f g
  let sq := IsPushout.of_hasPushout P.i d
  let := cofibration_of_isPushout sq
  let fsq := map_isPushout (F := F) sq
  let H := F.map P.π ≫ F.map f ≫ b
  have hb : F.map P.i ≫ H = F.map d ≫ b := by
    apply map_coprod_hom_ext F
    · simp only [H, ← F.map_comp_assoc, Precylinder.inl_i_assoc, d, coprod.inl_desc]
      rw [← Category.assoc, P.i₀_π, Category.id_comp]
    · simp only [H, ← F.map_comp_assoc, Precylinder.inr_i_assoc, d, coprod.inr_desc]
      rw [← Category.assoc, P.i₁_π, Category.id_comp]
      exact h
  let u := fsq.desc H b hb
  obtain ⟨Z, j, p, hj, hp, hjp⟩ := factorization (F := F) u
  let := hj
  let := hp
  let q := pushout.inr P.i d ≫ j
  have hqp : F.map q ≫ p = b := by
    rw [show q = pushout.inr P.i d ≫ j from rfl, F.map_comp, Category.assoc, hjp]
    exact fsq.inr_desc H b hb
  have hqw : WeakEquivalence q :=
    (weakEquivalence_map_iff (F := F) q).1 (weakEquivalence_of_postcomp_of_fac hqp)
  refine ⟨Z, q, inferInstance, hqw, P, hP, ⟨?_⟩⟩
  exact {
    h := pushout.inl P.i d ≫ j
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

/-- Lemma 6.1.2(1): equality after an ambient weak equivalence implies
left homotopy in the source. The ambient target need not be cofibrant. -/
theorem leftHomotopy_of_map_postcomp_eq
    {A B : C} [HasBinaryCoproduct A A] (f g : A ⟶ B)
    {X : D} (b : F.obj B ⟶ X) [WeakEquivalence b]
    (h : F.map f ≫ b = F.map g ≫ b) : ABCPrecofibrationCategory.LeftHomotopyRel f g := by
  let (A : C) : IsCofibrant A := source_cofibrant F A
  let d := coprod.desc f g
  obtain ⟨Z, i, p, hi, hp, hip⟩ := ABCPrecofibrationCategory.factorization d
  let := hi
  let := hp
  let f' := coprod.inl ≫ i
  let g' := coprod.inr ≫ i
  have hd : coprod.desc f' g' = i := by ext <;> simp [f', g']
  let : Cofibration (coprod.desc f' g') := hd.symm ▸ hi
  let := map_weakEquivalence F p
  have he : F.map f' ≫ (F.map p ≫ b) = F.map g' ≫ (F.map p ≫ b) := by
    simpa [f', g', ← F.map_comp_assoc, Category.assoc, hip, d] using h
  have hh := leftHomotopy_of_map_postcomp_eq_of_cofibration F f' g' (F.map p ≫ b) he
  simpa [f', g', Category.assoc, hip, d] using hh.postcomp p

/-- Cancellation in the source is detected by every functor inverting its
weak equivalences, not just by a chosen localization. -/
theorem map_eq_of_map_postcomp_eq
    {E : Type*} [Category E] (G : C ⥤ E)
    (hG : (weakEquivalences C).IsInvertedBy G)
    {A B : C} (f g : A ⟶ B) {X : D}
    (b : F.obj B ⟶ X) [WeakEquivalence b]
    (h : F.map f ≫ b = F.map g ≫ b) : G.map f = G.map g := by
  let (A : C) : IsCofibrant A := source_cofibrant F A
  let := hasBinaryCoproduct A A
  have hG' : (weakEquivalences (CofibrantObject C)).IsInvertedBy
      (CofibrantObject.ι ⋙ G) := by
    intro X Y w hw
    exact hG w.hom hw
  exact map_eq_of_cofibrant_leftHomotopy (CofibrantObject.ι ⋙ G) hG'
    (f := CofibrantObject.homMk f) (g := CofibrantObject.homMk g)
    (leftHomotopy_of_map_postcomp_eq F f g b h)

/-- Lemma 6.1.3(1): fractions with the same ambient numerator and denominator
have the same value under every functor inverting source weak equivalences.
The common-resolution argument avoids reducing denominators to trivial
cofibrations; the two resulting triangles commute up to left homotopy. -/
theorem fraction_map_eq_of_ambient_comparison
    {A B : C} (φ ψ : (weakEquivalences C).LeftFraction A B)
    {X : D} (p : F.obj φ.Y' ⟶ X) (q : F.obj ψ.Y' ⟶ X)
    [WeakEquivalence p] [WeakEquivalence q]
    (hf : F.map φ.f ≫ p = F.map ψ.f ≫ q)
    (hs : F.map φ.s ≫ p = F.map ψ.s ≫ q)
    {E : Type*} [Category E] (G : C ⥤ E)
    (hG : (weakEquivalences C).IsInvertedBy G) :
    φ.map G hG = ψ.map G hG := by
  obtain ⟨Z, i, j, r, _, hi, _, _, hr, hir, hjr⟩ := exists_common_resolution F p q
  let := hr
  have hsi : G.map (φ.s ≫ i) = G.map (ψ.s ≫ j) := by
    apply map_eq_of_map_postcomp_eq F G hG _ _ r
    simpa only [F.map_comp, Category.assoc, hir, hjr] using hs
  have hfi : G.map (φ.f ≫ i) = G.map (ψ.f ≫ j) := by
    apply map_eq_of_map_postcomp_eq F G hG _ _ r
    simpa only [F.map_comp, Category.assoc, hir, hjr] using hf
  let := hG _ φ.hs
  let : IsIso (G.map i) := hG i hi.mem
  have : IsIso (G.map (φ.s ≫ i)) := by rw [G.map_comp]; infer_instance
  apply (cancel_mono (G.map (φ.s ≫ i))).1
  calc
    φ.map G hG ≫ G.map (φ.s ≫ i) = G.map (φ.f ≫ i) := by
      simp only [G.map_comp]
      rw [← Category.assoc, φ.map_comp_map_s]
    _ = G.map (ψ.f ≫ j) := hfi
    _ = ψ.map G hG ≫ G.map (ψ.s ≫ j) := by
      simp only [G.map_comp]
      rw [← Category.assoc, ψ.map_comp_map_s]
    _ = ψ.map G hG ≫ G.map (φ.s ≫ i) := by rw [hsi]

end ABCCofibrations.IsCofibrantApproximation

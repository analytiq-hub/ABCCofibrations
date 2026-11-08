/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.HomotopyFractions
public import ABCCofibrations.CofibrantReplacement

/-!
# Independence of fraction choices over an ambient object

Lemma 6.1.3(1) for inclusion of cofibrant objects. The comparison weak
equivalences may take values in an arbitrary ambient object. A common
cofibrant extension and ambient cancellation identify the two fractions.
For trivial-cofibration denominators, a second proof uses their pushout.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type u'} [Category.{v'} D]

/-- Independence of fraction choices over an ambient object, Lemma 6.1.3(1)
for inclusion of cofibrant objects. Denominators need only be weak
equivalences. A common extension of the ambient comparison maps makes both
numerator and denominator triangles commute up to left homotopy. -/
theorem weakEquivalence_fraction_map_eq_of_ambient_comparison
    {X Y : CofibrantObject C}
    (φ ψ : (weakEquivalences (CofibrantObject C)).LeftFraction X Y)
    {B : C} (p : φ.Y'.obj ⟶ B) (q : ψ.Y'.obj ⟶ B)
    [WeakEquivalence p] [WeakEquivalence q]
    (hf : φ.f.hom ≫ p = ψ.f.hom ≫ q)
    (hs : φ.s.hom ≫ p = ψ.s.hom ≫ q)
    (F : CofibrantObject C ⥤ D)
    (hF : (weakEquivalences (CofibrantObject C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF := by
  obtain ⟨R, i, j, r, hR, _, hi, _, _, hr, hir, hjr⟩ :=
    exists_common_cofibrant_replacement p q
  let := hR
  let := hr
  let P := CofibrantObject.mk R
  let i' : φ.Y' ⟶ P := CofibrantObject.homMk i
  let j' : ψ.Y' ⟶ P := CofibrantObject.homMk j
  have hsi : F.map (φ.s ≫ i') = F.map (ψ.s ≫ j') := by
    apply map_eq_of_postcomp_ambient_weakEquivalence F hF _ _ r
    change (φ.s.hom ≫ i) ≫ r = (ψ.s.hom ≫ j) ≫ r
    simpa only [Category.assoc, hir, hjr] using hs
  have hfi : F.map (φ.f ≫ i') = F.map (ψ.f ≫ j') := by
    apply map_eq_of_postcomp_ambient_weakEquivalence F hF _ _ r
    change (φ.f.hom ≫ i) ≫ r = (ψ.f.hom ≫ j) ≫ r
    simpa only [Category.assoc, hir, hjr] using hf
  let := hF _ φ.hs
  let : IsIso (F.map i') := hF i' hi.mem
  have : IsIso (F.map (φ.s ≫ i')) := by rw [F.map_comp]; infer_instance
  apply (cancel_mono (F.map (φ.s ≫ i'))).1
  calc
    φ.map F hF ≫ F.map (φ.s ≫ i') = F.map (φ.f ≫ i') := by
      simp only [F.map_comp]
      rw [← Category.assoc, φ.map_comp_map_s]
    _ = F.map (ψ.f ≫ j') := hfi
    _ = ψ.map F hF ≫ F.map (ψ.s ≫ j') := by
      simp only [F.map_comp]
      rw [← Category.assoc, ψ.map_comp_map_s]
    _ = ψ.map F hF ≫ F.map (φ.s ≫ i') := by rw [hsi]

/-- Two trivial-cofibration fractions over the same ambient numerator and
denominator give equal arrows under every functor inverting trivial
cofibrations. The ambient comparison target need not be cofibrant. -/
theorem trivialCofibration_fraction_map_eq_of_ambient_comparison
    {X Y : CofibrantObject C}
    (φ ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y)
    {B : C} (p : φ.Y'.obj ⟶ B) (q : ψ.Y'.obj ⟶ B)
    [WeakEquivalence p] [WeakEquivalence q]
    (hf : φ.f.hom ≫ p = ψ.f.hom ≫ q)
    (hs : φ.s.hom ≫ p = ψ.s.hom ≫ q)
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF := by
  obtain ⟨hcs, hws⟩ := (mem_cofibrantTrivialCofibrations_iff φ.s).1 φ.hs
  obtain ⟨hct, hwt⟩ := (mem_cofibrantTrivialCofibrations_iff ψ.s).1 ψ.hs
  let := hcs
  let := hws
  let := hct
  let := hwt
  let sq := IsPushout.of_hasPushout φ.s.hom ψ.s.hom
  let := cofibration_of_isPushout sq
  let := weakEquivalence_of_isPushout sq
  let := cofibration_of_isPushout sq.flip
  let := weakEquivalence_of_isPushout sq.flip
  let := cofibrant_target (pushout.inr φ.s.hom ψ.s.hom)
  let P := CofibrantObject.mk (pushout φ.s.hom ψ.s.hom)
  let i : φ.Y' ⟶ P := CofibrantObject.homMk (pushout.inl φ.s.hom ψ.s.hom)
  let j : ψ.Y' ⟶ P := CofibrantObject.homMk (pushout.inr φ.s.hom ψ.s.hom)
  let : Cofibration i.hom := inferInstanceAs (Cofibration (pushout.inl φ.s.hom ψ.s.hom))
  let : WeakEquivalence i.hom :=
    inferInstanceAs (WeakEquivalence (pushout.inl φ.s.hom ψ.s.hom))
  let : Cofibration j.hom := inferInstanceAs (Cofibration (pushout.inr φ.s.hom ψ.s.hom))
  let : WeakEquivalence j.hom :=
    inferInstanceAs (WeakEquivalence (pushout.inr φ.s.hom ψ.s.hom))
  let r : P.obj ⟶ B := pushout.desc p q hs
  have hir : i.hom ≫ r = p := pushout.inl_desc _ _ _
  let : WeakEquivalence r := weakEquivalence_of_precomp_of_fac hir
  have hi : cofibrantTrivialCofibrations i :=
    (mem_cofibrantTrivialCofibrations_iff i).2 ⟨inferInstance, inferInstance⟩
  have hj : cofibrantTrivialCofibrations j :=
    (mem_cofibrantTrivialCofibrations_iff j).2 ⟨inferInstance, inferInstance⟩
  apply (trivialCofibration_fraction_map_eq_iff φ ψ i j hi hj
    (by ext; exact sq.w) F hF).2
  apply map_eq_of_postcomp_ambient_weakEquivalence F
    ((inverts_weakEquivalences_iff_inverts_trivialCofibrations F).2 hF)
    (φ.f ≫ i) (ψ.f ≫ j) r
  change (φ.f.hom ≫ pushout.inl _ _) ≫ r =
    (ψ.f.hom ≫ pushout.inr _ _) ≫ r
  simpa only [r, Category.assoc, pushout.inl_desc, pushout.inr_desc] using hf

end ABCCofibrations.ABCPrecofibrationCategory

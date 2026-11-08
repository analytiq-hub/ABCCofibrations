/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.HomotopyCategory

/-!
# Weak-equivalence laws on left-homotopy classes

Identities, composition, and two-out-of-three descend to the left-homotopy
quotient by choosing representatives and using homotopy invariance of weak
equivalence. These properties do not assume saturation of weak equivalences.
-/

public section

universe v u

open CategoryTheory HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [CategoryTheory.Limits.HasInitial C]
  [ABCPrecofibrationCategory C]

private theorem quotient_weakEquivalences_map_iff {X Y : CofibrantObject C} (f : X ⟶ Y) :
    weakEquivalences (LeftHomotopyCategory C) (toLeftHomotopyCategory.map f) ↔
      weakEquivalences (CofibrantObject C) f :=
  MorphismProperty.quotient_iff _ _ f

/-- Identity classes are weak equivalences. -/
instance weakEquivalences_leftHomotopyCategory_containsIdentities :
    (weakEquivalences (LeftHomotopyCategory C)).ContainsIdentities where
  id_mem := by
    rintro ⟨X⟩
    apply (quotient_weakEquivalences_map_iff (𝟙 X)).2
    change weakEquivalences C (𝟙 X.obj)
    exact (weakEquivalence_of_isIso (𝟙 X.obj)).mem

/-- Two-out-of-three holds for homotopy classes, because it holds on any
composable pair of representatives. Composition stability is included. -/
instance weakEquivalences_leftHomotopyCategory_twoOutOfThree :
    (weakEquivalences (LeftHomotopyCategory C)).HasTwoOutOfThreeProperty where
  comp_mem := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩ hf hg
    apply (quotient_weakEquivalences_map_iff (f ≫ g)).2
    exact (weakEquivalences (CofibrantObject C)).comp_mem f g
      ((quotient_weakEquivalences_map_iff f).1 hf)
      ((quotient_weakEquivalences_map_iff g).1 hg)
  of_postcomp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩ hg hfg
    apply (quotient_weakEquivalences_map_iff f).2
    exact (weakEquivalences (CofibrantObject C)).of_postcomp f g
      ((quotient_weakEquivalences_map_iff g).1 hg)
      ((quotient_weakEquivalences_map_iff (f ≫ g)).1 hfg)
  of_precomp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩ hf hfg
    apply (quotient_weakEquivalences_map_iff g).2
    exact (weakEquivalences (CofibrantObject C)).of_precomp f g
      ((quotient_weakEquivalences_map_iff f).1 hf)
      ((quotient_weakEquivalences_map_iff (f ≫ g)).1 hfg)

/-- The descended weak-equivalence class is multiplicative. -/
instance weakEquivalences_leftHomotopyCategory_isMultiplicative :
    (weakEquivalences (LeftHomotopyCategory C)).IsMultiplicative where
  id_mem := (weakEquivalences (LeftHomotopyCategory C)).id_mem
  comp_mem := (weakEquivalences (LeftHomotopyCategory C)).comp_mem

end ABCCofibrations.ABCPrecofibrationCategory

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.RightHomotopyCategory

/-!
# Weak-equivalence laws on right-homotopy classes

Identities, composition, and two-out-of-three descend to the right-homotopy
quotient by choosing representatives and using homotopy invariance of weak
equivalence. These properties do not assume saturation of weak equivalences.
-/

public section

universe v u

open CategoryTheory HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [CategoryTheory.Limits.HasTerminal C]
  [ABCPrefibrationCategory C]

private theorem quotient_weakEquivalences_map_iff {X Y : FibrantObject C} (f : X ⟶ Y) :
    weakEquivalences (RightHomotopyCategory C) (toRightHomotopyCategory.map f) ↔
      weakEquivalences (FibrantObject C) f :=
  MorphismProperty.quotient_iff _ _ f

/-- Identity classes are weak equivalences. -/
instance weakEquivalences_rightHomotopyCategory_containsIdentities :
    (weakEquivalences (RightHomotopyCategory C)).ContainsIdentities where
  id_mem := by
    rintro ⟨X⟩
    apply (quotient_weakEquivalences_map_iff (𝟙 X)).2
    change weakEquivalences C (𝟙 X.obj)
    exact (weakEquivalence_of_isIso (𝟙 X.obj)).mem

/-- Two-out-of-three holds for homotopy classes, because it holds on any
composable pair of representatives. Composition stability is included. -/
instance weakEquivalences_rightHomotopyCategory_twoOutOfThree :
    (weakEquivalences (RightHomotopyCategory C)).HasTwoOutOfThreeProperty where
  comp_mem := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩ hf hg
    apply (quotient_weakEquivalences_map_iff (f ≫ g)).2
    exact (weakEquivalences (FibrantObject C)).comp_mem f g
      ((quotient_weakEquivalences_map_iff f).1 hf)
      ((quotient_weakEquivalences_map_iff g).1 hg)
  of_postcomp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩ hg hfg
    apply (quotient_weakEquivalences_map_iff f).2
    exact (weakEquivalences (FibrantObject C)).of_postcomp f g
      ((quotient_weakEquivalences_map_iff g).1 hg)
      ((quotient_weakEquivalences_map_iff (f ≫ g)).1 hfg)
  of_precomp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩ hf hfg
    apply (quotient_weakEquivalences_map_iff g).2
    exact (weakEquivalences (FibrantObject C)).of_precomp f g
      ((quotient_weakEquivalences_map_iff f).1 hf)
      ((quotient_weakEquivalences_map_iff (f ≫ g)).1 hfg)

/-- The descended weak-equivalence class is multiplicative. -/
instance weakEquivalences_rightHomotopyCategory_isMultiplicative :
    (weakEquivalences (RightHomotopyCategory C)).IsMultiplicative where
  id_mem := (weakEquivalences (RightHomotopyCategory C)).id_mem
  comp_mem := (weakEquivalences (RightHomotopyCategory C)).comp_mem

end ABCCofibrations.ABCPrefibrationCategory

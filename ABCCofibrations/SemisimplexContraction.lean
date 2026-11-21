/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.SemisimplicialResolution
public import Mathlib.Order.Fin.Tuple

/-! # A categorical contraction of Δ′

An explicit zigzag id → shift ← const [0], without an initial-object claim.
This is the elementary vertex-insertion argument used in direct resolutions;
compare Szumiło, arXiv:1411.0303v1, Lemma 3.9 at n = 0. We insert at the
beginning instead of at the end.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace ABCCofibrations

/-- Extend an ordinal embedding by a new first vertex. -/
def semisimplexShiftMap {n m : SemiSimplexCategory} (f : n ⟶ m) :
    SemiSimplexCategory.mk (n.len + 1) ⟶ SemiSimplexCategory.mk (m.len + 1) :=
  SemiSimplexCategory.homEquiv.symm
    (OrderEmbedding.ofStrictMono
      (Fin.cons 0 (fun i ↦ (SemiSimplexCategory.homEquiv f i).succ))
      (Fin.strictMono_cons.2 ⟨fun _ ↦ by simp,
        Fin.strictMono_succ.comp (SemiSimplexCategory.homEquiv f).strictMono⟩))

/-- Adjoin a new first vertex to every ordinal. -/
def semisimplexShift : SemiSimplexCategory ⥤ SemiSimplexCategory where
  obj n := ⟨n.len + 1⟩
  map := semisimplexShiftMap
  map_id n := by
    apply SemiSimplexCategory.hom_ext
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp [semisimplexShiftMap]
  map_comp f g := by
    apply SemiSimplexCategory.hom_ext
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp [semisimplexShiftMap, SemiSimplexCategory.homEquiv_comp]

/-- Include all original vertices after the new first vertex. -/
def semisimplexToShift : 𝟭 SemiSimplexCategory ⟶ semisimplexShift where
  app n := SemiSimplexCategory.homEquiv.symm (Fin.succOrderEmb (n.len + 1))
  naturality n m f := by
    apply SemiSimplexCategory.hom_ext
    ext i
    simp [semisimplexShift, semisimplexShiftMap, SemiSimplexCategory.homEquiv_comp]

/-- Select the newly adjoined vertex, naturally in the ordinal. -/
def semisimplexPointToShift :
    (Functor.const SemiSimplexCategory).obj (SemiSimplexCategory.mk 0) ⟶ semisimplexShift where
  app n := SemiSimplexCategory.homEquiv.symm
    (OrderEmbedding.ofStrictMono (fun _ ↦ (0 : Fin (n.len + 2)))
      (fun i j h ↦ by fin_cases i; fin_cases j; simp at h))
  naturality n m f := by
    apply SemiSimplexCategory.hom_ext
    ext i
    fin_cases i
    rfl

end ABCCofibrations

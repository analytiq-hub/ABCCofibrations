/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.HomotopyIsomorphisms
public import ABCCofibrations.SequentialColimits
public import ABCCofibrations.FibrationCategory
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Saturation of weak equivalences (Lemma 7.2.2, Theorem 7.2.3)

A precofibration category satisfying CF6 has saturated weak equivalences: a map
which becomes an isomorphism in the homotopy category is a weak equivalence. In
particular, every cofibration category, and dually every fibration category, has
saturated weak equivalences.

Following the paper, it suffices to treat a cofibration `A₀ ⟶ A₁` with cofibrant
source. Lemma 7.2.1 produces a sequence of cofibrations `A₀ ⟶ A₁ ⟶ A₂ ⟶ ⋯` in
which every `Aₙ ⟶ Aₙ₊₂` is a weak equivalence. By CF6 applied to the even and the
odd subsequences, both `A₀ ⟶ colim Aₙ` and `A₁ ⟶ colim Aₙ` are weak
equivalences, so `A₀ ⟶ A₁` is one by two out of three. The subsequences are
compositions with final functors `ℕ ⥤ ℕ`, so their colimits are the colimit of
the whole sequence.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

namespace ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

namespace SaturationSequence

/-- A stage of the sequence: a cofibration with cofibrant source which becomes an
isomorphism in the homotopy category. -/
structure Stage where
  /-- The source. -/
  X : C
  /-- The target. -/
  Y : C
  /-- The cofibration. -/
  a : X ⟶ Y
  hX : IsCofibrant X
  ha : Cofibration a
  hiso : IsIso (L.map a)

variable {L}

lemma Stage.exists_next (s : Stage L) :
    ∃ (Z : C) (b : s.Y ⟶ Z), Cofibration b ∧ WeakEquivalence (s.a ≫ b) ∧ IsIso (L.map b) := by
  have := s.hX
  have := s.ha
  have := s.hiso
  have := cofibrant_target s.a
  obtain ⟨Z, b, hb, hw⟩ := (exists_leftInverse_iff L s.a).1 ⟨inv (L.map s.a), by simp⟩
  have := Localization.inverts L (weakEquivalences C) _ hw.mem
  refine ⟨Z, b, hb, hw, ?_⟩
  rw [show L.map b = inv (L.map s.a) ≫ L.map (s.a ≫ b) by simp]
  infer_instance

/-- The next stage. -/
noncomputable def Stage.next (s : Stage L) : Stage L where
  X := s.Y
  Y := s.exists_next.choose
  a := s.exists_next.choose_spec.choose
  hX := by
    have := s.hX
    have := s.ha
    exact cofibrant_target s.a
  ha := s.exists_next.choose_spec.choose_spec.1
  hiso := s.exists_next.choose_spec.choose_spec.2.2

lemma Stage.weakEquivalence_comp_next (s : Stage L) : WeakEquivalence (s.a ≫ s.next.a) :=
  s.exists_next.choose_spec.choose_spec.2.1

/-- The stages of the sequence. -/
noncomputable def stage (s : Stage L) : ℕ → Stage L
  | 0 => s
  | n + 1 => (stage s n).next

/-- The sequence of cofibrations. -/
noncomputable def seq (s : Stage L) : ℕ ⥤ C :=
  Functor.ofSequence (X := fun n ↦ (stage s n).X) fun n ↦ (stage s n).a

lemma seq_map_succ (s : Stage L) (n : ℕ) : (seq s).map (succHom n) = (stage s n).a :=
  Functor.ofSequence_map_homOfLE_succ _ n

lemma seq_weakEquivalence_two (s : Stage L) (n : ℕ) :
    WeakEquivalence ((seq s).map (succHom n) ≫ (seq s).map (succHom (n + 1))) := by
  have := (stage s n).weakEquivalence_comp_next
  simp only [seq_map_succ]
  exact this

end SaturationSequence

open SaturationSequence

/-- The functor `ℕ ⥤ ℕ`, `n ↦ k + 2n`. -/
def evenOdd (k : ℕ) : ℕ ⥤ ℕ := Monotone.functor (f := fun n ↦ k + 2 * n) (by
  intro a b h
  dsimp
  omega)

instance (k : ℕ) : (evenOdd k).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun d ↦ ⟨d, ⟨homOfLE (by dsimp [evenOdd]; omega)⟩⟩)
    (fun {_} {c} _ _ ↦ ⟨c, 𝟙 c, Subsingleton.elim _ _⟩)

include L in
/-- The key step of Lemma 7.2.2: assuming CF6, a cofibration with cofibrant source
which becomes an isomorphism in the homotopy category is a weak equivalence. -/
theorem weakEquivalence_of_cofibration_of_isIso (h1 : SequentialCofibrationAxiom C)
    (h2 : TrivialSequentialAxiom C) {A₀ A₁ : C} [IsCofibrant A₀] (a : A₀ ⟶ A₁)
    [Cofibration a] (hiso : IsIso (L.map a)) : WeakEquivalence a := by
  let s : Stage L := ⟨A₀, A₁, a, inferInstance, inferInstance, hiso⟩
  let F := seq s
  have hF0 : IsCofibrant (F.obj 0) := s.hX
  have hFs (n : ℕ) : Cofibration (F.map (succHom n)) := by
    rw [seq_map_succ]
    exact (stage s n).ha
  have := h1.hasColimit F hF0 hFs
  -- CF6 for the subsequence `n ↦ k + 2n`.
  have key (k : ℕ) : WeakEquivalence (colimit.ι F ((evenOdd k).obj 0)) := by
    let G := evenOdd k ⋙ F
    have hG (n : ℕ) : G.map (succHom n) = F.map (succHom (k + 2 * n)) ≫
        F.map (succHom (k + 2 * n + 1)) := by
      rw [← F.map_comp]
      rfl
    have hG0 : IsCofibrant (G.obj 0) := (stage s (k + 2 * 0)).hX
    have hGs (n : ℕ) : Cofibration (G.map (succHom n)) := by
      rw [hG]
      exact ⟨(cofibrations C).comp_mem _ _ (hFs (k + 2 * n)).mem (hFs (k + 2 * n + 1)).mem⟩
    have hGw (n : ℕ) : WeakEquivalence (G.map (succHom n)) := by
      rw [hG]
      exact seq_weakEquivalence_two s (k + 2 * n)
    have := h2 G hG0 hGs hGw
    have := weakEquivalence_of_isIso (Functor.Final.colimitIso (evenOdd k) F).hom
    rw [← Functor.Final.ι_colimitIso_hom (evenOdd k) F 0]
    infer_instance
  have h₀ : WeakEquivalence (colimit.ι F 0) := key 0
  have h₁ : WeakEquivalence (colimit.ι F (0 + 1)) := key 1
  have := weakEquivalence_of_postcomp_of_fac (colimit.w F (succHom 0))
  rwa [seq_map_succ] at this

include L in
/-- **Lemma 7.2.2(1).** In a precofibration category satisfying CF6, a map which
becomes an isomorphism in the homotopy category is a weak equivalence: the weak
equivalences are saturated. -/
theorem weakEquivalence_iff_isIso_map (h1 : SequentialCofibrationAxiom C)
    (h2 : TrivialSequentialAxiom C) {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ IsIso (L.map f) := by
  refine ⟨fun hf ↦ Localization.inverts L (weakEquivalences C) f hf.mem, fun hf ↦ ?_⟩
  obtain ⟨A₀, q, hA₀, hq⟩ := exists_cofibrant_replacement X
  have := hA₀
  obtain ⟨A₁, a, r, ha, hr, hfac⟩ := factorization (q ≫ f)
  have := ha
  have := Localization.inverts L (weakEquivalences C) q hq.mem
  have := Localization.inverts L (weakEquivalences C) r hr.mem
  have : IsIso (L.map a) := by
    rw [show L.map a = L.map (q ≫ f) ≫ inv (L.map r) by
      rw [← hfac, L.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
    simp only [L.map_comp]
    infer_instance
  have := weakEquivalence_of_cofibration_of_isIso L h1 h2 a this
  have : WeakEquivalence (q ≫ f) := by rw [← hfac]; infer_instance
  exact weakEquivalence_of_precomp q f

end ABCPrecofibrationCategory

/-- **Theorem 7.2.3(1).** A cofibration category has saturated weak
equivalences. -/
theorem ABCCofibrationCategory.weakEquivalence_iff_isIso_map {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
    [ABCCofibrationCategory C] {D : Type*} [Category D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ IsIso (L.map f) :=
  ABCPrecofibrationCategory.weakEquivalence_iff_isIso_map L
    ABCCofibrationCategory.sequentialCofibrationAxiom
    ABCCofibrationCategory.trivialSequentialAxiom f

section Fibration

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C]
  {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- **Lemma 7.2.2(2).** In a prefibration category satisfying F6 (CF6 in the
opposite category), the weak equivalences are saturated. -/
theorem ABCPrefibrationCategory.weakEquivalence_iff_isIso_map [ABCPrefibrationCategory C]
    (h1 : ABCPrecofibrationCategory.SequentialCofibrationAxiom Cᵒᵖ)
    (h2 : ABCPrecofibrationCategory.TrivialSequentialAxiom Cᵒᵖ) {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ IsIso (L.map f) := by
  have : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  rw [← weakEquivalences_op_iff, ← isIso_op_iff]
  exact ABCPrecofibrationCategory.weakEquivalence_iff_isIso_map L.op h1 h2 f.op

/-- **Theorem 7.2.3(2).** A fibration category has saturated weak
equivalences. -/
theorem ABCFibrationCategory.weakEquivalence_iff_isIso_map [ABCFibrationCategory C]
    {X Y : C} (f : X ⟶ Y) : WeakEquivalence f ↔ IsIso (L.map f) :=
  ABCPrefibrationCategory.weakEquivalence_iff_isIso_map L
    ABCCofibrationCategory.sequentialCofibrationAxiom
    ABCCofibrationCategory.trivialSequentialAxiom f

end Fibration

end ABCCofibrations

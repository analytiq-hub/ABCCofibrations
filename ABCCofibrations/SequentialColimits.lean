/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Gluing
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Tactic.TFAE

/-!
# Colimits of maps of CF6 sequences (Lemma 1.6.4(1))

A *CF6 sequence* is a functor `F : ℕ ⥤ C` with `F 0` cofibrant and all
successive maps cofibrations. Lemma 1.6.4(1): for a map `τ : F ⟶ G` of CF6
sequences which is a weak equivalence in each degree, the induced map of
colimits is a weak equivalence between cofibrant objects.

The axiom CF6 is split into its two parts, stated as standalone hypotheses
on a precofibration category, so that the lemma uses only CF1–CF4 and CF6
as in the paper (not CF5).

The proof has two steps, as in the paper.

* **Reedy step.** If every `τ_n` is a cofibration, `τ_0` is trivial, and every
  comparison `G_n ⊔_{F_n} F_{n+1} → G_{n+1}` is a trivial cofibration, then
  `colim τ` is a weak equivalence. With `A = colim F`, the objects
  `H_n = G_n ⊔_{F_n} A` form a CF6 sequence of trivial cofibrations: by
  pushout pasting, `H_n → H_{n+1}` is a cobase change of the comparison map.
  Its colimit is `colim G`, and `A → colim G` factors as
  `A → H_0 → colim H ≅ colim G`.
* **Reduction.** Inductively choose strengthened Brown factorizations
  `τ_n = r_n ∘ τ'_n`, `r_n ∘ σ_n = 1`, compatible along the sequences, using
  the cofibration-edge relative Brown factorization
  `exists_relative_brown_of_cofibration_edges`. Both `τ'` and `σ` satisfy the
  Reedy hypotheses, so their colimit maps are weak equivalences; two out of
  three then handles `colim r` and `colim τ`. This uses only the corrected
  form of the relative Brown factorization, not the separate comparison
  claims of Lemma 1.3.4(1) for arbitrary vertical maps.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- The successive map `n ⟶ n + 1` of `ℕ`. -/
abbrev succHom (n : ℕ) : n ⟶ n + 1 := homOfLE (Nat.le_succ n)

variable (C) in
/-- CF6(1): colimits of CF6 sequences exist, and the transfinite composite
from the first object is a cofibration. -/
structure SequentialCofibrationAxiom : Prop where
  hasColimit (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (succHom n))) : HasColimit F
  cofibration (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (succHom n))) [HasColimit F] : Cofibration (colimit.ι F 0)

variable (C) in
/-- CF6(2): the transfinite composite of a CF6 sequence of trivial
cofibrations is a weak equivalence. -/
def TrivialSequentialAxiom : Prop :=
  ∀ (F : ℕ ⥤ C), IsCofibrant (F.obj 0) → (∀ n, Cofibration (F.map (succHom n))) →
    (∀ n, WeakEquivalence (F.map (succHom n))) → ∀ [HasColimit F],
      WeakEquivalence (colimit.ι F 0)

/-- The colimit of a CF6 sequence is cofibrant. -/
theorem isCofibrant_colimit_of_sequence (h1 : SequentialCofibrationAxiom C) (F : ℕ ⥤ C)
    (h0 : IsCofibrant (F.obj 0)) (hf : ∀ n, Cofibration (F.map (succHom n)))
    [HasColimit F] : IsCofibrant (colimit F) := by
  let := h1.cofibration F h0 hf
  exact cofibrant_target (colimit.ι F 0)

namespace ReedyStep

variable {F G : ℕ ⥤ C} (τ : F ⟶ G) [HasColimit F]
  [∀ n, IsCofibrant (F.obj n)] [IsCofibrant (colimit F)] [∀ n, Cofibration (τ.app n)]

/-- `H_n = G_n ⊔_{F_n} colim F`. -/
noncomputable def obj (n : ℕ) : C := pushout (τ.app n) (colimit.ι F n)

/-- The structure map `G_n → H_n`. -/
noncomputable def inl (n : ℕ) : G.obj n ⟶ obj τ n := pushout.inl _ _

/-- The structure map `colim F → H_n`. -/
noncomputable def inr (n : ℕ) : colimit F ⟶ obj τ n := pushout.inr _ _

theorem condition (n : ℕ) : τ.app n ≫ inl τ n = colimit.ι F n ≫ inr τ n :=
  pushout.condition

theorem isPushout (n : ℕ) : IsPushout (τ.app n) (colimit.ι F n) (inl τ n) (inr τ n) :=
  IsPushout.of_hasPushout _ _

/-- The transition `H_n → H_{n+1}`. -/
noncomputable def map (n : ℕ) : obj τ n ⟶ obj τ (n + 1) :=
  pushout.desc (G.map (succHom n) ≫ inl τ (n + 1)) (inr τ (n + 1)) (by
    rw [← Category.assoc, ← τ.naturality, Category.assoc, condition, ← Category.assoc,
      colimit.w])

@[reassoc (attr := simp)]
theorem inl_map (n : ℕ) : inl τ n ≫ map τ n = G.map (succHom n) ≫ inl τ (n + 1) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_map (n : ℕ) : inr τ n ≫ map τ n = inr τ (n + 1) :=
  pushout.inr_desc _ _ _

/-- The sequence `n ↦ H_n`. -/
noncomputable def seq : ℕ ⥤ C := Functor.ofSequence (map τ)

theorem seq_map_succ (n : ℕ) : (seq τ).map (succHom n) = map τ n :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The first map `colim F → H_0` is a trivial cofibration when `τ_0` is. -/
theorem inr_zero_trivial [WeakEquivalence (τ.app 0)] :
    Cofibration (inr τ 0) ∧ WeakEquivalence (inr τ 0) :=
  ⟨cofibration_of_isPushout (isPushout τ 0), weakEquivalence_of_isPushout (isPushout τ 0)⟩

theorem isCofibrant_obj (n : ℕ) : IsCofibrant (obj τ n) := by
  let := cofibration_of_isPushout (isPushout τ n)
  exact cofibrant_target (inr τ n)

/-- Each transition of the pushout sequence is a cobase change of the relative comparison. -/
theorem isPushout_map (n : ℕ) {P : C} {l : G.obj n ⟶ P} {r : F.obj (n + 1) ⟶ P}
    (hP : IsPushout (τ.app n) (F.map (succHom n)) l r) (k : P ⟶ G.obj (n + 1))
    (hl : l ≫ k = G.map (succHom n)) (hr : r ≫ k = τ.app (n + 1)) :
    ∃ q : P ⟶ obj τ n, IsPushout k q (inl τ (n + 1)) (map τ n) := by
  have s : IsPushout (τ.app n) (F.map (succHom n) ≫ colimit.ι F (n + 1)) (inl τ n)
      (inr τ n) := by
    rw [colimit.w]
    exact isPushout τ n
  have sq₂ := IsPushout.of_top' s hP
  set q := hP.desc (inl τ n) (colimit.ι F (n + 1) ≫ inr τ n) _
  have hq₁ : l ≫ q = inl τ n := hP.inl_desc _ _ _
  have hq₂ : r ≫ q = colimit.ι F (n + 1) ≫ inr τ n := hP.inr_desc _ _ _
  have outer : IsPushout (r ≫ k) (colimit.ι F (n + 1)) (inl τ (n + 1))
      (inr τ n ≫ map τ n) := by
    rw [hr, inr_map]
    exact isPushout τ (n + 1)
  have comm : k ≫ inl τ (n + 1) = q ≫ map τ n := by
    apply hP.hom_ext
    · rw [reassoc_of% hl, reassoc_of% hq₁, inl_map]
    · rw [reassoc_of% hr, reassoc_of% hq₂, inr_map, condition]
  have sq₃ : IsPushout k q (inl τ (n + 1)) (map τ n) := IsPushout.of_left outer comm sq₂
  exact ⟨q, sq₃⟩

/-- The pushout sequence has cofibration transitions when the relative comparisons do. -/
theorem map_cofibration (n : ℕ) {P : C} {l : G.obj n ⟶ P} {r : F.obj (n + 1) ⟶ P}
    (hP : IsPushout (τ.app n) (F.map (succHom n)) l r) (k : P ⟶ G.obj (n + 1))
    (hl : l ≫ k = G.map (succHom n)) (hr : r ≫ k = τ.app (n + 1))
    [Cofibration k] : Cofibration (map τ n) := by
  obtain ⟨q, sq⟩ := isPushout_map τ n hP k hl hr
  have := cofibration_of_isPushout hP
  have := cofibrant_target r
  have := isCofibrant_obj τ n
  exact cofibration_of_isPushout sq

/-- Pushout pasting: each transition `H_n → H_{n+1}` is a cobase change of the
comparison map `G_n ⊔_{F_n} F_{n+1} → G_{n+1}`, so it is a cofibration, and a
weak equivalence when the comparison map is. -/
theorem map_trivial (n : ℕ) {P : C} {l : G.obj n ⟶ P} {r : F.obj (n + 1) ⟶ P}
    (hP : IsPushout (τ.app n) (F.map (succHom n)) l r) (k : P ⟶ G.obj (n + 1))
    (hl : l ≫ k = G.map (succHom n)) (hr : r ≫ k = τ.app (n + 1))
    [Cofibration k] [WeakEquivalence k] :
    Cofibration (map τ n) ∧ WeakEquivalence (map τ n) := by
  obtain ⟨q, sq⟩ := isPushout_map τ n hP k hl hr
  have := cofibration_of_isPushout hP
  have := cofibrant_target r
  have := isCofibrant_obj τ n
  exact ⟨cofibration_of_isPushout sq, weakEquivalence_of_isPushout sq⟩

section Colimit

section

variable [HasColimit (seq τ)]

/-- The colimit leg `H_n → colim H`, typed with `H_n = obj τ n`. -/
noncomputable def ι' (n : ℕ) : obj τ n ⟶ colimit (seq τ) := colimit.ι (seq τ) n

@[reassoc (attr := simp)]
theorem map_ι' (n : ℕ) : map τ n ≫ ι' τ (n + 1) = ι' τ n := by
  have := colimit.w (seq τ) (succHom n)
  rw [seq_map_succ] at this
  exact this

theorem hom_ext_seq {X : C} {f g : colimit (seq τ) ⟶ X} (h : ∀ n, ι' τ n ≫ f = ι' τ n ≫ g) :
    f = g :=
  colimit.hom_ext h

/-- The composite `colim F → H_n → colim H` does not depend on `n`. -/
theorem inr_ι (n : ℕ) : inr τ n ≫ ι' τ n = inr τ 0 ≫ ι' τ 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← ih, ← inr_map τ n, Category.assoc, map_ι']

end

variable [HasColimit G]

/-- The legs `H_n → colim G`. -/
noncomputable def toColimitG (n : ℕ) : obj τ n ⟶ colimit G :=
  pushout.desc (colimit.ι G n) (colimMap τ) (ι_colimMap τ n).symm

@[reassoc (attr := simp)]
theorem inl_toColimitG (n : ℕ) : inl τ n ≫ toColimitG τ n = colimit.ι G n :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_toColimitG (n : ℕ) : inr τ n ≫ toColimitG τ n = colimMap τ :=
  pushout.inr_desc _ _ _

theorem map_toColimitG (n : ℕ) : map τ n ≫ toColimitG τ (n + 1) = toColimitG τ n := by
  apply pushout.hom_ext
  · change inl τ n ≫ _ = inl τ n ≫ _
    rw [inl_map_assoc, inl_toColimitG, inl_toColimitG, colimit.w]
  · change inr τ n ≫ _ = inr τ n ≫ _
    rw [inr_map_assoc, inr_toColimitG, inr_toColimitG]

variable [HasColimit (seq τ)]

/-- `colim G` is a cocone over `H`. -/
noncomputable def coconeG : Cocone (seq τ) where
  pt := colimit G
  ι := NatTrans.ofSequence (fun n ↦ toColimitG τ n) (fun n ↦ by
    rw [seq_map_succ]
    exact (map_toColimitG τ n).trans (Category.comp_id _).symm)

/-- `colim H → colim G`. -/
noncomputable def ψ : colimit (seq τ) ⟶ colimit G := colimit.desc (seq τ) (coconeG τ)

/-- The natural map `G ⟶ H`. -/
noncomputable def inlNat : G ⟶ seq τ :=
  NatTrans.ofSequence (fun n ↦ inl τ n) (fun n ↦ by
    rw [seq_map_succ]
    exact (inl_map τ n).symm)

/-- `colim G → colim H`. -/
noncomputable def φ : colimit G ⟶ colimit (seq τ) := colimMap (inlNat τ)

@[reassoc]
theorem ι_φ (n : ℕ) : colimit.ι G n ≫ φ τ = inl τ n ≫ ι' τ n :=
  ι_colimMap _ n

@[reassoc]
theorem ι'_ψ (n : ℕ) : ι' τ n ≫ ψ τ = toColimitG τ n :=
  colimit.ι_desc _ n

/-- The colimit map of `τ`, followed by `colim G ≅ colim H`, is
`colim F → H_0 → colim H`. -/
theorem colimMap_φ : colimMap τ ≫ φ τ = inr τ 0 ≫ ι' τ 0 := by
  apply colimit.hom_ext
  intro m
  rw [ι_colimMap_assoc, ι_φ, ← inr_ι τ m, ← Category.assoc, condition, Category.assoc]

theorem φ_ψ : φ τ ≫ ψ τ = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  rw [ι_φ_assoc, ι'_ψ, Category.comp_id, inl_toColimitG]

theorem ψ_φ : ψ τ ≫ φ τ = 𝟙 _ := by
  apply hom_ext_seq
  intro n
  rw [ι'_ψ_assoc, Category.comp_id]
  apply pushout.hom_ext
  · change inl τ n ≫ _ = inl τ n ≫ _
    rw [inl_toColimitG_assoc]
    exact ι_φ τ n
  · change inr τ n ≫ _ = inr τ n ≫ _
    rw [inr_toColimitG_assoc, colimMap_φ, ← inr_ι τ n]

instance : IsIso (φ τ) := ⟨ψ τ, φ_ψ τ, ψ_φ τ⟩

end Colimit

end ReedyStep

/-- The relative comparison from the first pushout to the colimit is a
cofibration for a Reedy cofibration of sequences. The pushout may be any
representative, rather than the chosen categorical pushout. -/
theorem cofibration_comparison_colimit_of_reedy (h1 : SequentialCofibrationAxiom C)
    {F G : ℕ ⥤ C} (τ : F ⟶ G)
    (hF0 : IsCofibrant (F.obj 0)) (hF : ∀ n, Cofibration (F.map (succHom n)))
    (hτ : ∀ n, Cofibration (τ.app n))
    (hk : ∀ n, ∃ (P : C) (l : G.obj n ⟶ P) (r : F.obj (n + 1) ⟶ P) (k : P ⟶ G.obj (n + 1)),
      IsPushout (τ.app n) (F.map (succHom n)) l r ∧ l ≫ k = G.map (succHom n) ∧
        r ≫ k = τ.app (n + 1) ∧ Cofibration k)
    [HasColimit F] [HasColimit G] {P : C} {l : G.obj 0 ⟶ P} {r : colimit F ⟶ P}
    (hP : IsPushout (τ.app 0) (colimit.ι F 0) l r) (c : P ⟶ colimit G)
    (hl : l ≫ c = colimit.ι G 0) (hr : r ≫ c = colimMap τ) : Cofibration c := by
  have : ∀ n, IsCofibrant (F.obj n) := isCofibrant_obj_of_sequence F hF0 hF
  have : IsCofibrant (colimit F) := isCofibrant_colimit_of_sequence h1 F hF0 hF
  have : ∀ n, Cofibration (τ.app n) := hτ
  have hs (n : ℕ) : Cofibration ((ReedyStep.seq τ).map (succHom n)) := by
    obtain ⟨Q, l, r, k, hQ, hl, hr, hc⟩ := hk n
    rw [ReedyStep.seq_map_succ]
    exact ReedyStep.map_cofibration τ n hQ k hl hr
  have h0 : IsCofibrant ((ReedyStep.seq τ).obj 0) := ReedyStep.isCofibrant_obj τ 0
  have := h1.hasColimit (ReedyStep.seq τ) h0 hs
  have : Cofibration (ReedyStep.ι' τ 0) := h1.cofibration (ReedyStep.seq τ) h0 hs
  have := isCofibrant_colimit_of_sequence h1 (ReedyStep.seq τ) h0 hs
  have := cofibration_of_isIso (inv (ReedyStep.φ τ))
  let he : P ≅ ReedyStep.obj τ 0 := hP.isoPushout
  have hPC : IsCofibrant P := by
    have := cofibration_of_isPushout hP
    exact cofibrant_target r
  have := cofibration_of_isIso he.hom
  rw [show c = he.hom ≫ ReedyStep.ι' τ 0 ≫ inv (ReedyStep.φ τ) by
    apply hP.hom_ext
    · rw [hl, ← Category.assoc, show l ≫ he.hom = ReedyStep.inl τ 0 from hP.inl_isoPushout_hom]
      rw [← ReedyStep.ι_φ_assoc, IsIso.hom_inv_id, Category.comp_id]
    · rw [hr, ← Category.assoc, show r ≫ he.hom = ReedyStep.inr τ 0 from hP.inr_isoPushout_hom]
      rw [← Category.assoc, ← ReedyStep.colimMap_φ, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- Sequential colimits preserve Reedy cofibrations, using CF6(1). -/
theorem cofibration_colimMap_of_reedy (h1 : SequentialCofibrationAxiom C)
    {F G : ℕ ⥤ C} (τ : F ⟶ G)
    (hF0 : IsCofibrant (F.obj 0)) (hF : ∀ n, Cofibration (F.map (succHom n)))
    (hτ : ∀ n, Cofibration (τ.app n))
    (hk : ∀ n, ∃ (P : C) (l : G.obj n ⟶ P) (r : F.obj (n + 1) ⟶ P) (k : P ⟶ G.obj (n + 1)),
      IsPushout (τ.app n) (F.map (succHom n)) l r ∧ l ≫ k = G.map (succHom n) ∧
        r ≫ k = τ.app (n + 1) ∧ Cofibration k)
    [HasColimit F] [HasColimit G] : Cofibration (colimMap τ) := by
  have hFn : ∀ n, IsCofibrant (F.obj n) := isCofibrant_obj_of_sequence F hF0 hF
  have hA : IsCofibrant (colimit F) := isCofibrant_colimit_of_sequence h1 F hF0 hF
  have hτ' : ∀ n, Cofibration (τ.app n) := hτ
  have hs (n : ℕ) : Cofibration ((ReedyStep.seq τ).map (succHom n)) := by
    obtain ⟨P, l, r, k, hP, hl, hr, hc⟩ := hk n
    rw [ReedyStep.seq_map_succ]
    exact ReedyStep.map_cofibration τ n hP k hl hr
  have h0 : IsCofibrant ((ReedyStep.seq τ).obj 0) := ReedyStep.isCofibrant_obj τ 0
  have := h1.hasColimit (ReedyStep.seq τ) h0 hs
  have : Cofibration (ReedyStep.ι' τ 0) := h1.cofibration (ReedyStep.seq τ) h0 hs
  have := isCofibrant_colimit_of_sequence h1 (ReedyStep.seq τ) h0 hs
  have := cofibration_of_isPushout (ReedyStep.isPushout τ 0)
  have := cofibration_of_isIso (inv (ReedyStep.φ τ))
  rw [show colimMap τ = (ReedyStep.inr τ 0 ≫ ReedyStep.ι' τ 0) ≫
      inv (ReedyStep.φ τ) by
    rw [← ReedyStep.colimMap_φ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- The Reedy step of Lemma 1.6.4(1): if every component of `τ` is a
cofibration, `τ_0` is trivial, and every comparison map
`G_n ⊔_{F_n} F_{n+1} → G_{n+1}` is a trivial cofibration, then the colimit
map is a weak equivalence. The comparison may be computed from any pushout
representative. -/
theorem weakEquivalence_colimMap_of_reedy (h1 : SequentialCofibrationAxiom C)
    (h2 : TrivialSequentialAxiom C) {F G : ℕ ⥤ C} (τ : F ⟶ G)
    (hF0 : IsCofibrant (F.obj 0)) (hF : ∀ n, Cofibration (F.map (succHom n)))
    (hτ : ∀ n, Cofibration (τ.app n)) (hτ0 : WeakEquivalence (τ.app 0))
    (hk : ∀ n, ∃ (P : C) (l : G.obj n ⟶ P) (r : F.obj (n + 1) ⟶ P) (k : P ⟶ G.obj (n + 1)),
      IsPushout (τ.app n) (F.map (succHom n)) l r ∧ l ≫ k = G.map (succHom n) ∧
        r ≫ k = τ.app (n + 1) ∧ Cofibration k ∧ WeakEquivalence k)
    [HasColimit F] [HasColimit G] : WeakEquivalence (colimMap τ) := by
  have hFn : ∀ n, IsCofibrant (F.obj n) := isCofibrant_obj_of_sequence F hF0 hF
  have hA : IsCofibrant (colimit F) := isCofibrant_colimit_of_sequence h1 F hF0 hF
  have hτ' : ∀ n, Cofibration (τ.app n) := hτ
  have htr (n : ℕ) :
      Cofibration (ReedyStep.map τ n) ∧ WeakEquivalence (ReedyStep.map τ n) := by
    obtain ⟨P, l, r, k, hP, hl, hr, hkc, hkw⟩ := hk n
    exact ReedyStep.map_trivial τ n hP k hl hr
  have h0 : IsCofibrant ((ReedyStep.seq τ).obj 0) := ReedyStep.isCofibrant_obj τ 0
  have hs (n : ℕ) : Cofibration ((ReedyStep.seq τ).map (succHom n)) := by
    rw [ReedyStep.seq_map_succ]
    exact (htr n).1
  have hsw (n : ℕ) : WeakEquivalence ((ReedyStep.seq τ).map (succHom n)) := by
    rw [ReedyStep.seq_map_succ]
    exact (htr n).2
  have := h1.hasColimit (ReedyStep.seq τ) h0 hs
  have : WeakEquivalence (ReedyStep.ι' τ 0) := h2 (ReedyStep.seq τ) h0 hs hsw
  have := (ReedyStep.inr_zero_trivial τ).2
  have := weakEquivalence_of_isIso (ReedyStep.φ τ)
  have : WeakEquivalence (colimMap τ ≫ ReedyStep.φ τ) := by
    rw [ReedyStep.colimMap_φ]
    infer_instance
  exact weakEquivalence_of_postcomp (colimMap τ) (ReedyStep.φ τ)

/-- A strengthened Brown factorization `f = p ∘ i`, `p ∘ s = 1`, with `i` a
cofibration and `s` a trivial cofibration (Remark 1.3.2). -/
structure BrownData {A B : C} (f : A ⟶ B) where
  /-- The factorization object. -/
  Z : C
  /-- The cofibration. -/
  i : A ⟶ Z
  /-- The weak equivalence. -/
  p : Z ⟶ B
  /-- The trivial-cofibration section of `p`. -/
  s : B ⟶ Z
  isCofibrant_Z : IsCofibrant Z
  cofibration_i : Cofibration i
  weakEquivalence_p : WeakEquivalence p
  cofibration_s : Cofibration s
  weakEquivalence_s : WeakEquivalence s
  fac : i ≫ p = f
  sec : s ≫ p = 𝟙 B

theorem BrownData.nonempty {A B : C} [IsCofibrant A] [IsCofibrant B] (f : A ⟶ B) :
    Nonempty (BrownData f) := by
  obtain ⟨Z, i, p, s, hZ, hi, hp, hs, hsw, hip, hsp⟩ := exists_brown_factorization f
  exact ⟨⟨Z, i, p, s, hZ, hi, hp, hs, hsw, hip, hsp⟩⟩

theorem BrownData.weakEquivalence_i {A B : C} {f : A ⟶ B} (d : BrownData f)
    [WeakEquivalence f] : WeakEquivalence d.i := by
  have := d.weakEquivalence_p
  exact weakEquivalence_of_postcomp_of_fac d.fac

/-- One step of the inductive construction: a compatible factorization of
the next map, with both comparison maps trivial cofibrations. -/
structure BrownStep {A₁ A₂ B₁ B₂ : C} {f₁ : A₁ ⟶ B₁} (f₂ : A₂ ⟶ B₂)
    (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂) (d : BrownData f₁) where
  /-- The factorization of `f₂`. -/
  next : BrownData f₂
  /-- The map of factorization objects. -/
  c : d.Z ⟶ next.Z
  cofibration_c : Cofibration c
  i_c : d.i ≫ c = a ≫ next.i
  c_p : c ≫ next.p = d.p ≫ b
  s_c : d.s ≫ c = b ≫ next.s
  comparison_i : ∃ (P : C) (l : d.Z ⟶ P) (r : A₂ ⟶ P) (k : P ⟶ next.Z),
    IsPushout d.i a l r ∧ l ≫ k = c ∧ r ≫ k = next.i ∧ Cofibration k ∧ WeakEquivalence k
  comparison_s : ∃ (P : C) (l : d.Z ⟶ P) (r : B₂ ⟶ P) (k : P ⟶ next.Z),
    IsPushout d.s b l r ∧ l ≫ k = c ∧ r ≫ k = next.s ∧ Cofibration k ∧ WeakEquivalence k

/-- The step exists when the vertical maps are cofibrations and both
horizontal maps are weak equivalences. -/
theorem BrownStep.nonempty {A₁ A₂ B₁ B₂ : C} [IsCofibrant A₁] [IsCofibrant A₂]
    [IsCofibrant B₁] [IsCofibrant B₂] {f₁ : A₁ ⟶ B₁} (f₂ : A₂ ⟶ B₂)
    [WeakEquivalence f₁] [WeakEquivalence f₂]
    (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂) [Cofibration a] [Cofibration b] (h : f₁ ≫ b = a ≫ f₂)
    (d : BrownData f₁) : Nonempty (BrownStep f₂ a b d) := by
  have := d.cofibration_i
  have := d.weakEquivalence_p
  have := d.cofibration_s
  have := d.weakEquivalence_s
  have := d.weakEquivalence_i
  obtain ⟨Z₂, i₂, p₂, s₂, c, kA, kB, hZ₂, hi₂, hp₂, hs₂, hsw₂, hc, hkA, hkB, hkBw,
    hip₂, hsp₂, hic, hcp, hsc, hlA, hrA, hlB, hrB⟩ :=
    exists_relative_brown_of_cofibration_edges f₁ f₂ a b h d.i d.p d.s d.fac d.sec
  let next : BrownData f₂ := ⟨Z₂, i₂, p₂, s₂, hZ₂, hi₂, hp₂, hs₂, hsw₂, hip₂, hsp₂⟩
  have hi₂w : WeakEquivalence i₂ := next.weakEquivalence_i
  have hkAw : WeakEquivalence kA := by
    have := weakEquivalence_of_isPushout (IsPushout.of_hasPushout d.i a)
    exact weakEquivalence_of_precomp_of_fac hrA
  exact ⟨⟨next, c, hc, hic, hcp, hsc,
    ⟨_, _, _, kA, IsPushout.of_hasPushout d.i a, hlA, hrA, hkA, hkAw⟩,
    ⟨_, _, _, kB, IsPushout.of_hasPushout d.s b, hlB, hrB, hkB, hkBw⟩⟩⟩

namespace Reduction

variable {F G : ℕ ⥤ C} (τ : F ⟶ G) [∀ n, IsCofibrant (F.obj n)] [∀ n, IsCofibrant (G.obj n)]
  [∀ n, Cofibration (F.map (succHom n))] [∀ n, Cofibration (G.map (succHom n))]
  [∀ n, WeakEquivalence (τ.app n)]

/-- The inductively chosen factorizations of `τ_n`. -/
noncomputable def data : (n : ℕ) → BrownData (τ.app n)
  | 0 => Classical.choice (BrownData.nonempty _)
  | n + 1 => (Classical.choice (BrownStep.nonempty (τ.app (n + 1)) (F.map (succHom n))
      (G.map (succHom n)) (τ.naturality _).symm (data n))).next

/-- The step from degree `n` to `n + 1`. -/
noncomputable def step (n : ℕ) :
    BrownStep (τ.app (n + 1)) (F.map (succHom n)) (G.map (succHom n)) (data τ n) :=
  Classical.choice (BrownStep.nonempty (τ.app (n + 1)) (F.map (succHom n))
    (G.map (succHom n)) (τ.naturality _).symm (data τ n))

theorem data_succ (n : ℕ) : data τ (n + 1) = (step τ n).next := rfl

/-- The sequence of factorization objects. -/
noncomputable def seq : ℕ ⥤ C :=
  Functor.ofSequence (X := fun n ↦ (data τ n).Z) (fun n ↦ (step τ n).c)

theorem seq_map_succ (n : ℕ) : (seq τ).map (succHom n) = (step τ n).c :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The cofibration part `F ⟶ G'`. -/
noncomputable def incl : F ⟶ seq τ :=
  NatTrans.ofSequence (fun n ↦ (data τ n).i) (fun n ↦ by
    rw [seq_map_succ]
    exact ((step τ n).i_c).symm)

/-- The retraction part `G' ⟶ G`. -/
noncomputable def retr : seq τ ⟶ G :=
  NatTrans.ofSequence (fun n ↦ (data τ n).p) (fun n ↦ by
    rw [seq_map_succ]
    exact (step τ n).c_p)

/-- The section `G ⟶ G'`. -/
noncomputable def sect : G ⟶ seq τ :=
  NatTrans.ofSequence (fun n ↦ (data τ n).s) (fun n ↦ by
    rw [seq_map_succ]
    exact ((step τ n).s_c).symm)

theorem incl_retr : incl τ ≫ retr τ = τ := by
  ext n
  exact (data τ n).fac

theorem sect_retr : sect τ ≫ retr τ = 𝟙 G := by
  ext n
  exact (data τ n).sec

end Reduction

/-- **Lemma 1.6.4(1).** Assume CF1–CF4 and CF6. A map of CF6 sequences which
is a weak equivalence in every degree induces a weak equivalence of colimits.
The colimits are cofibrant by `isCofibrant_colimit_of_sequence`. -/
theorem weakEquivalence_colimMap_of_sequences (h1 : SequentialCofibrationAxiom C)
    (h2 : TrivialSequentialAxiom C) {F G : ℕ ⥤ C} (τ : F ⟶ G)
    (hF0 : IsCofibrant (F.obj 0)) (hF : ∀ n, Cofibration (F.map (succHom n)))
    (hG0 : IsCofibrant (G.obj 0)) (hG : ∀ n, Cofibration (G.map (succHom n)))
    (hw : ∀ n, WeakEquivalence (τ.app n)) [HasColimit F] [HasColimit G] :
    WeakEquivalence (colimMap τ) := by
  have hFn : ∀ n, IsCofibrant (F.obj n) := isCofibrant_obj_of_sequence F hF0 hF
  have hGn : ∀ n, IsCofibrant (G.obj n) := isCofibrant_obj_of_sequence G hG0 hG
  have hF' : ∀ n, Cofibration (F.map (succHom n)) := hF
  have hG' : ∀ n, Cofibration (G.map (succHom n)) := hG
  have hw' : ∀ n, WeakEquivalence (τ.app n) := hw
  let G' := Reduction.seq τ
  have hG'0 : IsCofibrant (G'.obj 0) := (Reduction.data τ 0).isCofibrant_Z
  have hG's (n : ℕ) : Cofibration (G'.map (succHom n)) := by
    rw [Reduction.seq_map_succ]
    exact (Reduction.step τ n).cofibration_c
  have := h1.hasColimit G' hG'0 hG's
  -- The cofibration part satisfies the Reedy hypotheses.
  have hincl : WeakEquivalence (colimMap (Reduction.incl τ)) := by
    refine weakEquivalence_colimMap_of_reedy h1 h2 _ hF0 hF
      (fun n ↦ (Reduction.data τ n).cofibration_i) (Reduction.data τ 0).weakEquivalence_i
      (fun n ↦ ?_)
    obtain ⟨P, l, r, k, hP, hl, hr, hk, hkw⟩ := (Reduction.step τ n).comparison_i
    exact ⟨P, l, r, k, hP, hl.trans (Reduction.seq_map_succ τ n).symm, hr, hk, hkw⟩
  -- So does the section.
  have hsect : WeakEquivalence (colimMap (Reduction.sect τ)) := by
    refine weakEquivalence_colimMap_of_reedy h1 h2 _ hG0 hG
      (fun n ↦ (Reduction.data τ n).cofibration_s) (Reduction.data τ 0).weakEquivalence_s
      (fun n ↦ ?_)
    obtain ⟨P, l, r, k, hP, hl, hr, hk, hkw⟩ := (Reduction.step τ n).comparison_s
    exact ⟨P, l, r, k, hP, hl.trans (Reduction.seq_map_succ τ n).symm, hr, hk, hkw⟩
  have hsr : colimMap (Reduction.sect τ) ≫ colimMap (Reduction.retr τ) = 𝟙 _ := by
    apply colimit.hom_ext
    intro n
    rw [ι_colimMap_assoc, ι_colimMap, ← Category.assoc, ← NatTrans.comp_app,
      Reduction.sect_retr, Category.comp_id]
    simp
  have hretr : WeakEquivalence (colimMap (Reduction.retr τ)) := by
    have : WeakEquivalence (𝟙 (colimit G)) := weakEquivalence_of_isIso _
    exact weakEquivalence_of_precomp_of_fac hsr
  have hir : colimMap (Reduction.incl τ) ≫ colimMap (Reduction.retr τ) = colimMap τ := by
    apply colimit.hom_ext
    intro n
    rw [ι_colimMap_assoc, ι_colimMap, ← Category.assoc, ← NatTrans.comp_app,
      Reduction.incl_retr, ι_colimMap]
  rw [← hir]
  infer_instance

variable (C) in
/-- The conclusion of Lemma 1.6.4(1), as a property of the category. -/
def ColimitWeakEquivalenceProperty : Prop :=
  ∀ {F G : ℕ ⥤ C} (τ : F ⟶ G), IsCofibrant (F.obj 0) →
    (∀ n, Cofibration (F.map (succHom n))) → IsCofibrant (G.obj 0) →
      (∀ n, Cofibration (G.map (succHom n))) → (∀ n, WeakEquivalence (τ.app n)) →
        ∀ [HasColimit F] [HasColimit G], WeakEquivalence (colimMap τ)

variable (C) in
/-- The conclusion of Lemma 1.6.4(1) for maps of sequences which are trivial
cofibrations in every degree. -/
def ColimitTrivialCofibrationProperty : Prop :=
  ∀ {F G : ℕ ⥤ C} (τ : F ⟶ G), IsCofibrant (F.obj 0) →
    (∀ n, Cofibration (F.map (succHom n))) → IsCofibrant (G.obj 0) →
      (∀ n, Cofibration (G.map (succHom n))) →
        (∀ n, Cofibration (τ.app n) ∧ WeakEquivalence (τ.app n)) →
          ∀ [HasColimit F] [HasColimit G], WeakEquivalence (colimMap τ)

/-- The transfinite composite of a CF6 sequence is the colimit map from the
constant sequence on its first object; this gives (c) ⟹ (a) in Lemma 1.6.5(1). -/
theorem trivialSequentialAxiom_of_colimitTrivialCofibrationProperty
    (h1 : SequentialCofibrationAxiom C) (h : ColimitTrivialCofibrationProperty C) :
    TrivialSequentialAxiom C := by
  intro F h0 hf hw _
  let K := (Functor.const ℕ).obj (F.obj 0)
  have hK0 : IsCofibrant (K.obj 0) := h0
  have hKs (n : ℕ) : Cofibration (K.map (succHom n)) := by
    let := h0
    exact cofibration_of_isIso (𝟙 (F.obj 0))
  have := h1.hasColimit K hK0 hKs
  let τ : K ⟶ F :=
    { app := fun n ↦ F.map (homOfLE (Nat.zero_le n))
      naturality := fun m n g ↦ by
        simp only [K, Functor.const_obj_map, ← F.map_comp]
        exact (Category.id_comp _).trans (congrArg F.map (Subsingleton.elim _ _)) }
  have hτ (n : ℕ) : Cofibration (τ.app n) ∧ WeakEquivalence (τ.app n) :=
    ⟨cofibration_map_of_le F h0 hf _, weakEquivalence_map_of_le F hw _⟩
  have hcm := h τ hK0 hKs h0 hf hτ
  have hiso : IsIso (colimit.ι K 0) := by
    refine ⟨colimit.desc K ⟨F.obj 0, 𝟙 K⟩, colimit.ι_desc _ _, ?_⟩
    apply colimit.hom_ext
    intro n
    rw [colimit.ι_desc_assoc, Category.comp_id]
    change 𝟙 _ ≫ colimit.ι K 0 = colimit.ι K n
    rw [Category.id_comp]
    exact (colimit.w K (homOfLE (Nat.zero_le n))).symm.trans (Category.id_comp _)
  have := weakEquivalence_of_isIso (colimit.ι K 0)
  have heq : colimit.ι K 0 ≫ colimMap τ = colimit.ι F 0 := by
    rw [ι_colimMap]
    change F.map (homOfLE (Nat.zero_le 0)) ≫ _ = _
    rw [show homOfLE (Nat.zero_le 0) = 𝟙 0 from Subsingleton.elim _ _, F.map_id,
      Category.id_comp]
  rw [← heq]
  infer_instance

/-- **Lemma 1.6.5(1)**, the equivalent formulations of CF6(2): given CF1–CF4
and CF6(1), the following are equivalent:
(a) CF6(2);
(b) the conclusion of Lemma 1.6.4(1);
(c) the conclusion of Lemma 1.6.4(1) for degreewise trivial cofibrations. -/
theorem trivialSequentialAxiom_tfae (h1 : SequentialCofibrationAxiom C) :
    List.TFAE [TrivialSequentialAxiom C, ColimitWeakEquivalenceProperty C,
      ColimitTrivialCofibrationProperty C] := by
  tfae_have 1 → 2 := fun h2 _ _ τ hF0 hF hG0 hG hw _ _ ↦
    weakEquivalence_colimMap_of_sequences h1 h2 τ hF0 hF hG0 hG hw
  tfae_have 2 → 3 := fun h _ _ τ hF0 hF hG0 hG hτ _ _ ↦
    h τ hF0 hF hG0 hG (fun n ↦ (hτ n).2)
  tfae_have 3 → 1 := trivialSequentialAxiom_of_colimitTrivialCofibrationProperty h1
  tfae_finish

end ABCCofibrations.ABCPrecofibrationCategory

namespace ABCCofibrations.ABCCofibrationCategory

open ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]

/-- CF6(1) of a cofibration category, in the standalone form. -/
theorem sequentialCofibrationAxiom [ABCCofibrationCategory C] :
    SequentialCofibrationAxiom C :=
  ⟨hasSequentialColimit, fun F h0 hf _ ↦ sequential_cofibration F h0 hf⟩

/-- CF6(2) of a cofibration category, in the standalone form. -/
theorem trivialSequentialAxiom [ABCCofibrationCategory C] : TrivialSequentialAxiom C :=
  fun F h0 hf hw _ ↦ sequential_weakEquivalence F h0 hf hw

/-- Lemma 1.6.4(1) in a cofibration category. -/
theorem weakEquivalence_colimMap_of_sequences [ABCCofibrationCategory C] {F G : ℕ ⥤ C}
    (τ : F ⟶ G) (hF0 : IsCofibrant (F.obj 0)) (hF : ∀ n, Cofibration (F.map (succHom n)))
    (hG0 : IsCofibrant (G.obj 0)) (hG : ∀ n, Cofibration (G.map (succHom n)))
    (hw : ∀ n, WeakEquivalence (τ.app n)) [HasColimit F] [HasColimit G] :
    WeakEquivalence (colimMap τ) :=
  ABCPrecofibrationCategory.weakEquivalence_colimMap_of_sequences sequentialCofibrationAxiom
    trivialSequentialAxiom τ hF0 hF hG0 hG hw

end ABCCofibrations.ABCCofibrationCategory
